package firrtl.passes

import scala.collection.mutable.{ArrayBuffer,HashMap}
import firrtl._
import firrtl.ir._
import firrtl.Mappers._
import firrtl.Utils._ 

object NoInlineMem extends Pass {

  val connects = HashMap[String, Expression]()
  val repl = HashMap[String, Expression]()
  val refs = HashMap[String, Expression]()
  val stmts = ArrayBuffer[Statement]()
  
  def name = "Replace Memory with BlackBox + Configuration File"

  // Explain???
  def getMemFields(mem: DefMemory): Seq[Field] = {
    val memType = get_type(mem).asInstanceOf[BundleType]
    val memFields = memType.fields flatMap { f => {
      val exps = create_exps(WRef(f.name, f.tpe, ExpKind(), times(f.flip, MALE)))
      exps map ( e =>
        Field(LowerTypes.loweredName(e), toFlip(gender(e)).flip, tpe(e))
      )
    }}
    memFields.toSeq
  }

  def getMemPorts(mem: DefMemory): Seq[Port] = {
    val memType = get_type(mem).asInstanceOf[BundleType]

    val blah = memType.fields map { f =>
      Port(mem.info, f.name, Input, f.tpe)
    }

    println(blah)


    val memFields = getMemFields(mem)
    memFields map { f => {
      // TODO: less complicated
      val dir = to_dir(swap(times(f.flip,MALE)))
      Port(mem.info,f.name,dir,f.tpe)
    }}

   // blah

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

        // MEMORY SPECIFIC
        // WSubField( WSubField (WRef ( name, type, kind, gender), name, type, gender), name, type, gender)


        def replaceExpr(e: Expression): Expression = {
          // WSubField(exp: Expression, name: String, tpe: Type, gender: Gender)
          //WSubField(refs("mem"),"T_3_data",UIntType(IntWidth(32)),FEMALE)
          /*e match {
            case WSubField(WRef(ref, _, kind, _), field, tpe, gen) => {
              kind match {
                case MemKind(_) => println("THIS IS MEMORY")
                case x => println("THIS IS NOT MEMORY")
              }

              // println("KIND: " + kind) 

              //if (tpe == MemKind()) println("THIS IS MEMORY")
            } 
            case e => e map replaceExpr
          }   
          e*/

          e match {
            case WSubField(WSubField( WRef(modname,_,MemKind(_),_),topPortName,_,_),sigName,sigType,gender) => {
              println("WOOOO IS MEMORY")
              e
              WSubField(refs("mem"),topPortName + "_" + sigName, sigType, gender)
              //WSubField()

            }
            case e => e
          }



        }







        

        s map onStmt match {
          case mem: DefMemory => {
            val moduleName = moduleNamespace.newName(mem.name)
            val memBlackBox = toBlackBox(moduleName, mem)
            newModules += memBlackBox    
            println("FIELDS: " + getMemFields(mem))
            // WRef(name: String, tpe: Type, kind: Kind, gender: Gender)
            //refs += WRef(moduleName,BundleType(getMemFields(mem)),NodeKind(),MALE)
            refs("mem") = WRef("mem", BundleType(getMemFields(mem)), InstanceKind(), MALE)

            // WDefInstance(info: Info, (inst) name: String, module: String, tpe: Type)  
            // DefMemory has nested WSubField, use flattened to match ExtModule    
            WDefInstance(memBlackBox.info,mem.name,moduleName,BundleType(getMemFields(mem)))
            //mem
          }  
          case c: Connect => {
            val info = c.info
            val loc = replaceExpr(c.loc)
            val expr = replaceExpr(c.expr)
            println("CONNECT: " + c.serialize)
            println("CONNECT INFO: " + c.info)
            Connect(info,loc,expr)
            //c

          }
          case s => s
        }  
      }

      val modifiedModules = m.copy(body = onStmt(m.body))
      newModules.toSeq :+ modifiedModules
    }

    val actualModules = c.modules flatMap {
      case m: Module => updateModule(m)
      case m: ExtModule => Seq(m)
    } map {
      // EmptyStmt
      case m: Module => m.copy(body = Utils.squashEmpty(m.body))
      case m: ExtModule => m
    }

    println("MODULES: ")
    actualModules foreach {x => println(x.serialize)}
    // Circuit(info: Info, modules: Seq[DefModule], main: String)
    Circuit(c.info, actualModules, c.main) 

  }

}