import scala.collection.immutable.HashMap
import scala.io.Source
def printHelp: Unit =
  println("help")

def readFile:String => Array[String] = name => Source.fromFile(name).getLines.toArray
 
@main
def test() = main("examples/wrong/infinite_recursion.adt")  
 
@main
def main(file:String) =
  try
    val ast = new AST(readFile(file))
    val np = Parser.parseProgram(ast.program)
    val interpreter = new Interpreter(np)
    (ast.program.expr zip interpreter.evaledExpr) foreach (
      (x, y) => println(x.toString + "\u001b[33m =\u001b[0m " + y.toString)
    )
  catch
    case e:CompilerException => System.err.println(e.getMessage)
