//get_type

package firrtl.passes

import scala.collection.mutable.{ArrayBuffer,HashMap}
import firrtl._
import firrtl.ir._
import firrtl.Mappers._
import firrtl.Utils._ 

object NoInlineMem extends Pass {

  def name = "Replace Memory with BlackBox + Configuration File"
  val newRefs = HashMap[String, Expression]()
  val newStatements = ArrayBuffer[Statement]()

  def memToBlackBox (name: String, mem: DefMemory): ExtModule = {
    val memPorts = getMemPorts(mem)
    ExtModule(mem.info,name,memPorts)
  }

  def getMemPorts(mem: DefMemory): Seq[Port] = {
    val memFields = getMemFields(mem)
    memFields map { f => {
      // LESS COMPLICATED
      val dir = to_dir(swap(times(f.flip,MALE)))
      Port(mem.info,f.name,dir,f.tpe)
    }}
  }

  // Shorten?
  def getMemFields(mem: DefMemory): Seq[Field] = {

    def loweredName(e: Expression): String = {

      val delim = "_"

      val out = e match {
        case e: WRef => e.name
        case e: WSubField => loweredName(e.exp) + delim + e.name
        case e: WSubIndex => {
          if (e.value == 0) loweredName(e.exp)
          else ""
          //loweredName(e.exp) + delim //+ e.value
        }
      }
      //println("NEWNAME:" + out)
      out

    }

    val memType = get_type(mem).asInstanceOf[BundleType]


    println("QQQ" + memType)
    println("RRR" + mem.serialize)
    println("SSS" + mem)

    val memFields = memType.fields flatMap { f => {
      val exps = create_exps(WRef(f.name, f.tpe, ExpKind(), times(f.flip, MALE)))
      exps map ( e =>
        Field(loweredName(e), toFlip(gender(e)).flip, tpe(e))
      )
    }}
    memFields.toSeq
  }

  def replaceMemPortRef(e: Expression): Expression = {
    //println("CONNECT EXPR:" + e)
    e match {
      // Mem has nested subfields
      // WSubField( WSubField (WRef ( name, type, kind, gender), name, type, gender), name, type, gender)
      case WSubField(WSubField(WRef(modName,_,MemKind(_),_),readerWriterName,_,_),sigName,sigType,gender) => {
        //println("CONNECT EXPR MEM:" + e.serialize)
        //println("MEM NAME: " + modName + "_" + readerWriterName + "_" + sigName)



        WSubField(newRefs(modName),readerWriterName + "_" + sigName, sigType, gender)
      }
      case WSubIndex(_,_,_,_) => EmptyExpression
      case e => e
    }
    //e
  }

  def run(c: Circuit): Circuit = {
    lazy val moduleNamespace = Namespace(c)

    def updateModules (m: Module) : Seq[DefModule] = {
      val newModules = ArrayBuffer[DefModule]()

      def onStmt(s: Statement): Statement = {

        //println(s.serialize)


        //println(s)


        s map onStmt match {
          case mem: DefMemory => {

            val moduleName = moduleNamespace.newName(mem.name)

            //println("OLDMEM: " + mem.serialize)

            val memBlackBox = memToBlackBox(moduleName, mem)
            newModules += memBlackBox    

            //println("NEWMEM: " + memBlackBox.serialize)

            //println("MODULE: " + memBlackBox.serialize)


            // WRef(name: String, tpe: Type, kind: Kind, gender: Gender)
            newRefs(mem.name) = WRef(moduleName, BundleType(getMemFields(mem)), InstanceKind(), MALE)
            // WDefInstance(info: Info, (inst) name: String, module: String, tpe: Type)  
            // DefMemory has nested WSubField, use flattened to match ExtModule    
            val out = WDefInstance(NoInfo,moduleName,moduleName,BundleType(getMemFields(mem)))

            //println("WDEFINSTANCE: " + out.serialize)
            out
            //mem
          }  
          case n: DefNode => {
            //println(n.serialize)
            n match {
              case DefNode(_,_,DoPrim(bits,_,_,_)) => println("blah")
              case n => 
            }
            //n
            n match {
              //case DefNode(_,_,DoPrim(bits,_,_,_)) => EmptyStmt
              case DefNode(_,"T_1011",_) => DefNode(NoInfo,"T_1011",UIntLiteral(0,IntWidth(1)))
              case DefNode(_,"T_1031",_) => DefNode(NoInfo,"T_1031",UIntLiteral(0,IntWidth(1)))
              case DefNode(_,"T_1051",_) => DefNode(NoInfo,"T_1051",UIntLiteral(0,IntWidth(1)))
              case DefNode(_,"T_1071",_) => DefNode(NoInfo,"T_1071",UIntLiteral(0,IntWidth(1)))
              case n => n
            }

            //EmptyStmt
          }
          case c: Connect => {
            //println("CONNECT: " + c.serialize)
            val info = c.info
            val loc = replaceMemPortRef(c.loc)
            val expr = replaceMemPortRef(c.expr)
            if (loc == EmptyExpression || expr == EmptyExpression){
              EmptyStmt
            }
            else Connect(info,loc,expr)
            //c
          }
          case s => s
        }  

      }
      val modifiedModules = m.copy(body = onStmt(m.body))
      newModules.toSeq :+ modifiedModules
    }

    val newModules = c.modules flatMap {
      case m: Module => updateModules(m)
      case m: ExtModule => Seq(m)
    } map {
      // EmptyStmt
      case m: Module => m.copy(body = Utils.squashEmpty(m.body))
      case m: ExtModule => m
    }

    /*newModules flatMap {
      case m: Module => Seq({println(m.body); m.body})
      case m: ExtModule => Seq(EmptyStmt)
    }*/

    /*newModules flatMap { x => x match {
      case m: Module => {println(m.body.serialize);Seq(m)}
      case m: ExtModule => Seq(m)
      //println(x.body.serialize)
    }}*/


    // Circuit(info: Info, modules: Seq[DefModule], main: String)
    val xxx = Circuit(c.info, newModules, c.main) 
    //println(xxx)
    xxx

  }

}