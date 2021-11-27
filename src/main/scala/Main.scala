import scala.collection.immutable.HashMap
import scala.io.Source
def printHelp: Unit =
  println("help")

def readFile:String => Array[String] = name => Source.fromFile(name).getLines.toArray
@main 
def test:Unit = main(Array[String]("test.adt"))
def main: Array[String] => Unit = args => args match
  case Array() => printHelp
  case x => 
    //parse compiler options
    if x.length == 1 then
      val ast = new AST(readFile(x(0)))
      val np = Parser.parseProgram(ast.program)
      np.adts.foreach(x => 
        val adt = x.asInstanceOf[ADT]
        println(adt.name)
        println("ops: ")
        adt.ops.foreach(x =>
          val y = x.asInstanceOf[Operation]
          print(y.name + " takes (" + y.par.length + "): ")
          y.par.foreach(z => print(z + " "))
          print("returns " + y.ret)
          println()
        )
        println("axs: ")
        adt.axs.foreach(println)
      )
  case _ => printHelp
