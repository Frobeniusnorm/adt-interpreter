import scala.collection.immutable.HashMap
import scala.io.Source
def printHelp: Unit =
  println("help")

def readFile:String => Array[String] = name => Source.fromFile(name).getLines.toArray
@main
def main: Array[String] => Unit = args => args match
  case Array() => printHelp
  case x => 
    //parse compiler options
    if x.length == 1 then
      val ast = new AST(readFile(x(0)))
      val np = Parser.parseProgram(ast.program)
      val interpreter = new Interpreter(np)
      (ast.program.expr zip interpreter.evaledExpr) foreach (
        (x, y) => println(x.toString + " = " + y.toString)
      )
