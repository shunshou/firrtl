package firrtl.passes

import scala.collection.mutable.{ArrayBuffer}
import firrtl._
import firrtl.ir._
import firrtl.Mappers._
import firrtl.Utils._ 

object NoInlineMem extends Pass {
  
  def name = "Replace Memory with BlackBox + Configuration File"

  private class LoweringCompiler extends Compiler {
    def transforms(ignore: java.io.Writer) = Seq(
      new IRToWorkingIR,
      new ResolveAndCheck,
      new HighFirrtlToMiddleFirrtl,
      new MiddleFirrtlToLowFirrtl
    )
  }

  def getMemFields(mem: DefMemory): Seq[Field] = {
    val memType = get_type(mem).asInstanceOf[BundleType]
    memType.fields flatMap { f => {
      val exps = create_exps(WRef(f.name, f.tpe, ExpKind(), times(f.flip, MALE)))
      exps map ( e =>
        Field(LowerTypes.loweredName(e), toFlip(gender(e)).flip, tpe(e))
      )
    }}
  }

  def getMemPorts(mem: DefMemory): Seq[Port] = {
    val memType = get_type(mem).asInstanceOf[BundleType]
    val memFields = getMemFields(mem)
    memFields map { f => {
      val dir = to_dir(swap(times(f.flip,MALE)))
      println(f.name)
      println(f.tpe)
      println(dir)
      Port(mem.info,f.name,dir,f.tpe)
    }}
  }

  def toBlackBox (name: String, mem: DefMemory): ExtModule = {
    val memPorts = getMemPorts(mem)
    ExtModule(mem.info,name,memPorts)
  }

















  






  def run(c: Circuit): Circuit = {
    lazy val moduleNamespace = Namespace(c)

    def updateModule (m: Module) : Seq[DefModule] = {
    val newModules = collection.mutable.ArrayBuffer[DefModule]()

    def onStmt(s: Statement): Statement = {
      s map onStmt match {
        case mem: DefMemory => {
          val moduleName = moduleNamespace.newName(mem.name + "_Mem")
          val memBlackBox = toBlackBox(moduleName, mem)
          newModules += memBlackBox          
            

            println(BundleType(getMemFields(mem)))
            WDefInstance(mem.info, mem.name, moduleName, get_type(mem))

            //WDefInstance(mem.info, mem.name, moduleName, s)

            //WDefInstance(mem.info, mem.name, moduleName, BundleType(getMemFields(mem)))
            //mem



          }  
          case s => s
        }  
    }


    val modifiedModules = m.copy(body = onStmt(m.body))
    newModules.toSeq :+ modifiedModules
  }


    

    // CONNECT? REF?

    // remove T_3 subfield
    //type mismatch?









    val actualModules = c.modules flatMap {
      case m: Module => updateModule(m)
      case m: ExtModule => Seq(m)
    } map {
      case m: Module => m.copy(body = Utils.squashEmpty(m.body))
      case m: ExtModule => m
    }

    

    val out = Circuit(c.info, actualModules, c.main) 

     val compiler = new LoweringCompiler
    // TODO don't use null
    //compiler.compile(Circuit(c.info, actualModules, c.main),new firrtl.Annotations.AnnotationMap(Seq.empty), null).circuit

    out
  }

}