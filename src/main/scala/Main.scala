import scala.collection.immutable.HashMap
import scala.io.Source
def printHelp: Unit =
  println("help")

def readFile:String => Array[String] = name => Source.fromFile(name).getLines.toArray
/*
test2.combine(test1.c2, test2.c2)
test1.combine(test1.c1, test2.c3)
*/
/* @main
def test() = main("examples/correct/namespaces.adt") */

@main
def main(file:String) =
  val ast = new AST(readFile(file))
  val np = Parser.parseProgram(ast.program)
  val interpreter = new Interpreter(np)
  (ast.program.expr zip interpreter.evaledExpr) foreach (
    (x, y) => println(x.toString + "\u001b[33m =\u001b[0m " + y.toString)
  )
