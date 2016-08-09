package firrtl.passes

import scala.collection.mutable.{ArrayBuffer,HashMap}
import firrtl._
import firrtl.ir._
import firrtl.Mappers._
import firrtl.Utils._
import firrtl.PrimOps._

object ReplaceSeqMems extends Pass {

  def name = "Replace Sequential Memories with Blackbox + Configuration File"
  
  val smemNames = ArrayBuffer[String]()
  val newModules = ArrayBuffer[DefModule]()

  def replaceSmemRef(e: Expression): Expression = {
    e map replaceSmemRef match {
      case WRef(name,tpe,MemKind(_),gender) if smemNames.contains(name) => {
        // WRef name == instance name
        WRef(name,tpe,InstanceKind(),gender)
      }
      case e => e
    }
  }

  def updateModules(m: Module): Seq[DefModule] = {
    def updateStmts(s: Statement): Statement = s map updateStmts map replaceSmemRef 
    val updatedModule = m.copy(body = updateStmts(replaceSmem(m.body)))
    newModules.toSeq :+ updatedModule
  }

  def run(c: Circuit) = {
    lazy val moduleNamespace = Namespace(c)

    val updatedModules = c.modules flatMap {
      case m: Module => updateModules(m)
      case m: ExtModule => Seq(m)
    } map {
      case m: Module => m.copy(body = Utils.squashEmpty(m.body))
      case m: ExtModule => m
    }

    smemNames foreach { n =>
      moduleNamespace.newName(n)
      moduleNamespace.newName(n + "_ext")
    }  

    uniqueMems foreach { x => 
      println(x.m.serialize)
    }  

    Circuit(c.info, updatedModules, c.main)
  }

  case class MemProto(
    name: String,
    dataType: String,
    depth: Int,
    writeLatency: Int,
    readLatency: Int,
    numReaders: Int,
    numWriters: Int,
    numRWriters: Int,
    m: DefMemory
    // TODO: read under write
  )
  def create_proto(m: DefMemory) = {
    uniqueMems += MemProto(
      m.name + "_ext",
      m.dataType.serialize,
      m.depth,
      m.writeLatency,
      m.readLatency,
      m.readers.length,
      m.writers.length,
      m.readwriters.length,
      m
    )
  }

  val uniqueMems = ArrayBuffer[MemProto]()

  def replaceSmem(s: Statement): Statement = {
    s map replaceSmem match {
      case m: DefMemory if m.readLatency > 0 => {
        val memType = get_type(m).asInstanceOf[BundleType]
        newModules += createSmemMod(m,memType)
        smemNames += m.name
        val instName = m.name
        WDefInstance(m.info, instName, m.name, memType)
      }
      case s => s
    }
  }

  // Derived from create_exps
  def flattenMemVec(dataBlockWidth:BigInt, e: Expression): Seq[Expression] = {
    Utils.tpe(e) match {
      case t:BundleType => {
        t.fields.flatMap { f => 
          flattenMemVec(dataBlockWidth,WSubField(e,f.name,f.tpe,times(gender(e), f.flip))) 
        }
      }
      case t:VectorType => {
        // All vecs concatenated (TODO: should possibly be conditionally in the future?)
        // Check vec sizes equal
        val vecSize = t.size
        val newType = t.tpe match {
          case x: SIntType => SIntType(IntWidth(vecSize * dataBlockWidth)) 
          case x: UIntType => UIntType(IntWidth(vecSize * dataBlockWidth))
        }
        val name = e.asInstanceOf[WSubField].name
        val ref = e.asInstanceOf[WSubField].exp
        if (name == "data" || name == "mask")
          Seq(WSubField(ref,name,newType,gender(e)))
        else Seq(e)
      }
      case t => Seq(e)
    }
  }

  // Other types not supported? TODO
  // All R,W,RWers should have the same type?
  // Check that mask Vec length matches data Vec length TODO
  def baseWidth(dataType: Type) : BigInt = {
    dataType match {
      case t: SIntType => t.width.asInstanceOf[IntWidth].width
      case t: UIntType => t.width.asInstanceOf[IntWidth].width
      case t: VectorType => baseWidth(t.tpe)
      case t => -1
    }
  }

  def baseTypeWithNewWidth(t: Type, width: BigInt): Type = {
    t match {
    case x: SIntType => SIntType(IntWidth(width)) 
    case x: UIntType => UIntType(IntWidth(width))
    }
  }

  def catVec(t: VectorType, inName: String, inGender: Gender, outName: String) : Seq[Statement] = {
    // Maybe I don't need to cat? TODO
    val delim = "_"
    val newStmts = ArrayBuffer[Statement]()
    val blockWidth = baseWidth(t.tpe)
    (0 until t.size-1) foreach { i =>
      // TODO: Add to namespace?
      val tempNodeName = outName + "_merge" + i
      val high = WRef(inName + delim + (i+1),t.tpe,PortKind(),inGender)
      val low = {
        if (i == 0) WRef(inName + delim + (i),t.tpe,PortKind(),inGender)
        else {
          val prevNodeName = newStmts.last.asInstanceOf[DefNode].name
          val prevNodeType = baseTypeWithNewWidth(t.tpe,blockWidth*(i+1))
          WRef(prevNodeName,prevNodeType,NodeKind(),inGender)
        }
      }
      val newType = baseTypeWithNewWidth(t.tpe,blockWidth*(i+2))
      newStmts += DefNode(NoInfo,tempNodeName,DoPrim(Cat,ArrayBuffer(high,low),ArrayBuffer(),newType))
    }
    newStmts.toSeq
  }

  def map_connect (intPorts:Expression, extRef: WRef, nameMap: Map[String,String], blockWidth: Int) : Seq[Statement] = {

    val delim = "_"
    val intGender = gender(intPorts)

    // Map from Int R/W/RW port name to Ext name
    def lowerExtName(e: Expression): String = e match {
      case e: WRef => nameMap(e.name)
      case e: WSubField => lowerExtName(e.exp) + delim + e.name
      case e: WSubIndex => lowerExtName(e.exp) + delim + e.value
    }

    val memModStmts = ArrayBuffer[Statement]()

    tpe(intPorts) match {
      case t: BundleType => {
        t.fields.flatMap {f => 
          val bundleStmt = map_connect(WSubField(intPorts,f.name,f.tpe,times(gender(intPorts),f.flip)),extRef,nameMap, blockWidth)
          memModStmts ++= bundleStmt
          bundleStmt
        }
      }
      case t: VectorType => {

        // TODO: Should only be UInt/SInt?
        val loweredIntName = LowerTypes.loweredName(intPorts)
        val loweredExtName = lowerExtName(intPorts)
        val name = intPorts.asInstanceOf[WSubField].name
        val flattenedWidth = t.size * blockWidth
        val finalType = baseTypeWithNewWidth(t.tpe,flattenedWidth)
  
        if (name == "mask") {

          // TODO: Mask should always be input?
          val maskExpandName = loweredExtName + "_expand"
          val maskExpandType = VectorType(UIntType(IntWidth(1)),flattenedWidth)
          // TODO: Add to namespace
          val maskExpand = DefWire(NoInfo,maskExpandName,maskExpandType)
          memModStmts += maskExpand
          val maskExpr = WRef(maskExpandName,maskExpandType,WireKind(),swap(intGender)) 
          (0 until flattenedWidth) foreach { i =>
            val extLoc = WSubIndex(maskExpr,i,maskExpandType,swap(intGender))
            val intLoc = WSubIndex(intPorts,i / blockWidth,UIntType(IntWidth(1)),intGender)
            memModStmts += Connect(NoInfo,extLoc,intLoc)
          } 
          memModStmts ++= catVec(maskExpandType, maskExpandName, swap(intGender),loweredExtName)
          val extLoc = WSubField(extRef,loweredExtName,finalType,intGender)
          val intLoc = WRef(memModStmts.last.asInstanceOf[DefNode].name,finalType,NodeKind(),swap(intGender))
          memModStmts += Connect(NoInfo,extLoc,intLoc)
        }
        if (name == "data"){
          val extLoc = WSubField(extRef,loweredExtName,finalType,swap(intGender))
          if (intGender == MALE){
            // Write port (blackbox has write data ports concatenated)
            memModStmts ++= catVec(t,loweredIntName,intGender,loweredExtName)
            val intLoc = WRef(memModStmts.last.asInstanceOf[DefNode].name,finalType,NodeKind(),intGender)
            memModStmts += Connect(NoInfo,extLoc,intLoc)
          }
          else {
            (0 until t.size) foreach { i =>
              val intLoc = WRef(loweredIntName + delim + (i),t.tpe,PortKind(),intGender)  
              val extract = DoPrim(Bits,ArrayBuffer(extLoc),ArrayBuffer(blockWidth*(i+1)-1,blockWidth*i),t.tpe)
              memModStmts += Connect(NoInfo,intLoc,extract)
            }  
          }
        }
        // TODO: Anything else that can be a Vec? besides data/mask
      }
      case t => {
        val extLoc = WSubField(extRef,lowerExtName(intPorts),t,swap(intGender))
        memModStmts += {
          if (intGender == FEMALE) Connect(NoInfo,intPorts,extLoc)
          else Connect(NoInfo,extLoc,intPorts)
        }
      }

    }
    memModStmts.toSeq
  }  

  def createSmemMod(m: DefMemory, tpe: BundleType): Module = {

    println(m.serialize)
    //println(m)

    val dataBlockWidth = baseWidth(m.dataType)

    val readers = m.readers.zipWithIndex.map{case (r,i) => (r,"R"+i)}
    val writers = m.writers.zipWithIndex.map{case (w,i) => (w,"W"+i)}
    val readwriters = m.readwriters.zipWithIndex.map{case (rw,i) => (rw,"RW"+i)}
    val memPortNames = (readers ++ writers ++ readwriters).toMap

    val memModStmts = ArrayBuffer[Statement]()

    val memPorts = tpe.fields map { f =>
      Port(m.info,f.name,to_dir(toGender(f.flip)),f.tpe)
    }

    //val memPorts = memPortsTemp :+ Port(m.info,"reset",Input,UIntType(IntWidth(1)))

    /*val blackBoxPorts = tpe.fields flatMap { f =>
      val exps = create_exps(WRef(memPortNames(f.name), f.tpe, PortKind(), toGender(f.flip)))
      exps map ( e => Port(m.info, LowerTypes.loweredName(e), to_dir(gender(e)), Utils.tpe(e)) )
    }*/
    
    val blackBoxPorts = tpe.fields flatMap { f =>
      val exps = flattenMemVec(dataBlockWidth,WRef(memPortNames(f.name), f.tpe, PortKind(), toGender(f.flip)))
      exps map ( e => Port(m.info, LowerTypes.loweredName(e), to_dir(gender(e)), Utils.tpe(e)) )
    }

    val blackBoxName = m.name + "_ext"
    val memBlackBox = ExtModule(m.info,blackBoxName,blackBoxPorts)
    val blackBoxType = module_type(memBlackBox)
    val blackBoxRef = WRef(blackBoxName,blackBoxType,InstanceKind(),MALE)

   if (uniqueMems.isEmpty){
      // Is this uniquely identifiable
      create_proto(m)
      newModules += memBlackBox
      memModStmts += WDefInstance(m.info,blackBoxName,blackBoxName,blackBoxType)
    }
    else {
      
      val duplicate = uniqueMems.find(p => {
        (p.dataType == m.dataType.serialize) && 
        (p.depth == m.depth) && 
        (p.writeLatency == m.writeLatency) && 
        (p.readLatency == m.readLatency) && 
        (p.numReaders == m.readers.length) && 
        (p.numWriters == m.writers.length) && 
        (p.numRWriters == m.readwriters.length) 
      })

      if (duplicate == None){
        create_proto(m)
        newModules += memBlackBox
        memModStmts += WDefInstance(m.info,blackBoxName,blackBoxName,blackBoxType)
      }
      else {
        val oldModName = duplicate.get.name
        memModStmts += WDefInstance(m.info,blackBoxName,oldModName,blackBoxType)
      }
    }  
  
    val connections = memPorts flatMap { p => 
      map_connect(WRef(p.name,p.tpe,PortKind(),to_gender(p.direction)),blackBoxRef,memPortNames,dataBlockWidth.intValue)
    }

    /*
    val connections = memPorts flatMap { p => 
      val intName = p.name
      val outName = memPortNames(p.name)
      val gender = to_gender(p.direction)
      val intExps = create_exps(WRef(intName,p.tpe,PortKind(),gender))
      val outExps = create_exps(WRef(outName,p.tpe,PortKind(),gender))
      intExps.zip(outExps).map{case (i,o) => {
        val gender = i match {
          case w: WSubField => w.gender
          case w: WSubIndex => w.gender
          case w => UNKNOWNGENDER
        }
        val intLoc = WRef(LowerTypes.loweredName(i),i.tpe,PortKind(),gender)
        val outLoc = WSubField(blackBoxRef,LowerTypes.loweredName(o),o.tpe,swap(gender))
        if (gender == FEMALE) Connect(NoInfo,intLoc,outLoc)
        else Connect(NoInfo,outLoc,intLoc)
      }}
    }
    */

    connections foreach {c => memModStmts += c}

    //println(Block(memModStmts.toList).serialize)

    Module(m.info,m.name,memPorts,Block(memModStmts.toList))

  }

}

// TODO: Mem tiling pass?

















//////////////////////////////////////////////////////////////
// Extra reset
// WR port, no mask