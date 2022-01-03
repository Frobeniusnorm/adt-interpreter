import scala.collection.immutable.HashMap
import scala.io.Source
def helpMsg = 
  """
ADT - Interpreter 

Usage: java -jar <executable> <adt file>
Where <executable> represents the .jar file of this program and <adt file> is a text file which contains adts and the expressions which should be evaluated.

Some error Messages explained:
Interpreter Errors:
- "Infinite Recursion: Axioms will be applied infinite times on this term!"
 During evaluation the interpreter applied axioms and one expression that was already evaluated appeared again.
 Further evaluation would never stop (since it would lead to an infinite loop).
- "Could not find fulfilling case predicate!"
 During the evaluation of a equation with multiple cases, no case was fulfilled, therefor the equation cannot be evaluated. 
 Maybe you missed an 'else' case?
  """

def readFile:String => Array[String] = name => Source.fromFile(name).getLines.toArray
 
/* @main
def test() = main("examples/wrong/infinite_recursion.adt")   */
class ArgumentParser(args:Seq[String]): 
  val (file, flags) =
    if (args contains "-help") || (args contains "--help") then
      println(helpMsg)
      (None, None)
    else
      val poss = args filter (!_.startsWith("-"))
      if poss.length > 1 then
        throw new ParserException("Multiple files given on command line! For help start this program with the -help flag")
      if poss.length == 0 then 
        throw new ParserException("No file given on command line! For help start this program with the -help flag")
      (Some(poss(0)), Some(args filter (_.startsWith("-"))))

@main
def main(arguments:String*) =
  val ap = ArgumentParser(arguments)
  if !ap.file.isEmpty then
    if ap.flags.get.length > 0 then throw new ParserException("Unknown passed flag(s):" + ap.flags.get.fold("")(_ + " " + _))
    try
      val ast = new AST(readFile(ap.file.get))
      val np = Parser.parseProgram(ast.program)
      val interpreter = new Interpreter(np)
      (ast.program.expr zip interpreter.evaledExpr) foreach (
        (x, y) => println(x.toString + "\u001b[33m =\u001b[0m " + y.toString)
      )
    catch
      case e:CompilerException => System.err.println(e.getMessage)
