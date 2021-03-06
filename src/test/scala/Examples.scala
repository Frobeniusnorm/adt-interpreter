import java.io.File
import scala.io.Source
import org.scalatest._
import matchers.should._
import Inspectors._
import org.scalatest.flatspec.AnyFlatSpec
import org.scalatest.funsuite.AnyFunSuite
def readFile:String => Array[String] = name => Source.fromFile(name).getLines.toArray
class ExamplesTest extends AnyFunSuite with Matchers:
    val positives = new File("examples/correct/").listFiles
    test("positives"){
      forEvery(positives){
        x =>
          try
            val pp =Parser.parseProgram(new AST(readFile(x.getPath)).program) 
            pp shouldNot be (null)
            Interpreter(pp)
            println(x.getName + " passed")
          catch
            case e => fail("File \"" + x.getName + "\" was not compiled correctly! " + e.getClass + ": " + e.getMessage + " in " + e.getStackTrace.foldLeft("")((o, a) => o + "\n" + a.toString))
      }
    }
    val negatives = new File("examples/wrong/").listFiles
    test("negatives"){
      forEvery(negatives){
          x =>
            var didAnError = true
            try
              val pp = Parser.parseProgram(new AST(readFile(x.getPath)).program) 
              pp shouldNot be (null)
              Interpreter(pp)
              didAnError = false
            catch
              case e => println(x.getName + " passed")
            if(!didAnError) fail("File \"" + x.getName + "\" was compiled correctly, although it contains errors!")
      }
    }
    val results = new File("examples/withResults/").listFiles.groupBy(x => x.getName.split("\\.")(0))
    test("results"){
      forEvery(results){
        x => 
          val res = x._2.filter(x => x.getName.endsWith("result"))(0)
          val adt = x._2.filter(x => x.getName.endsWith("adt"))(0)
          val ast = new AST(readFile(adt.getPath))
          val np = Parser.parseProgram(ast.program)
          val interpreter = new Interpreter(np)

          val expects = readFile(res.getPath)
          val test = (interpreter.results zip expects) 
          for (z,y) <- test do
            if z.toString.replaceAll("\u001B\\[[;\\d]*m", "") != y then
              fail("Wrong evaluated expression in Test: \"" + x._1 + "\", expected: \"" + y + "\" got: \"" + z.toString + "\"")
          println("Passed \"" + x._1 + "\"")
      }
    }
