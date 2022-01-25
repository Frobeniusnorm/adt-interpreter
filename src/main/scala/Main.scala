import scala.collection.immutable.HashMap
import scala.io.Source
import scala.collection.immutable.HashSet
def helpMsg = 
  """
ADT - Interpreter 

Usage: java -jar <executable> <adt file>
Where <executable> represents the .jar file of this program and <adt file> is a text file which contains adts and the expressions which should be evaluated.
Flags:
  - "-d" or "--debug" start the interpreter in debug mode
  - "--nocolor" deactivates color codes
  - "-v" or "--verbose" additionally shows the original expression that was evaluated
  """

def readFile:String => Array[String] = name => Source.fromFile(name).getLines.toArray

val allowedFlags = HashSet("--help", "-help", "-d", "-h", "--debug", "--nocolor", "-v", "--verbose")

@main
def test() = main("examples/correct/quicksort.adt")

class ArgumentParser(args:Seq[String]): 
  val (file, flags) =
    if (args contains "-help") || (args contains "--help") || (args contains "--h")then
      println(helpMsg)
      (None, None)
    else
      val poss = args filter (!_.startsWith("-"))
      if poss.length > 1 then
        throw new ParserException("Multiple files given on command line! For help start this program with the -help flag")
      if poss.length == 0 then 
        throw new ParserException("No file given on command line! For help start this program with the -help flag")
      (Some(poss(0)), Some(HashSet.from(args filter (_.startsWith("-")))))

def log(color:Boolean)(str:String) = 
    if color then println(str) 
    else 
        println (str.replaceAll("\u001b\\[32m", "").replaceAll("\u001b\\[33m", "").replaceAll("\u001b\\[0m", "")
                        .replaceAll("\u001b\\[36m", "").replaceAll("\u001b\\[35m", ""))
@main
def main(arguments:String*) =
  val ap = ArgumentParser(arguments)
  if !ap.file.isEmpty then
    if !ap.flags.get.forall(allowedFlags contains (_)) then throw new ParserException("Unknown passed flag(s):" + ap.flags.get.fold("")(_ + " " + _))
    val docolor = log(!ap.flags.get.contains("--nocolor"))(_)
    try
      val indebug = ap.flags.get.contains("-d") || ap.flags.get.contains("--debug")
      val verbose = indebug || ap.flags.get.contains("-v") || ap.flags.get.contains("--verbose")
      if indebug then
        println("[started in debug modus, evaluation will be paused and verbosly printed. Press Enter each time to continue evaluation]")
      val ast = new AST(readFile(ap.file.get))
      val np = Parser.parseProgram(ast.program)
      val interpreter = new Interpreter(np, indebug, docolor)
      (ast.program.expr zip interpreter.evaledExpr) foreach (
        (x, y) => docolor((if verbose then x.toString + "\u001b[33m =\u001b[0m " else "") + interpreter.replaceConstants(y.toString))
      )
    catch
      case e:CompilerException => docolor(e.getMessage)
