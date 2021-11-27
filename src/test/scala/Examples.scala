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
            Parser.parseProgram(new AST(readFile(x.getPath)).program) shouldNot be (null)
            println(x.getName + " passed")
          catch
            case e => fail("File \"" + x.getName + "\" was not compiled correctly!" + e.getMessage)
      }
    }
    val negatives = new File("examples/wrong/").listFiles
    test("negatives"){
      forEvery(negatives){
          x =>
            try
              Parser.parseProgram(new AST(readFile(x.getPath)).program) shouldNot be (null)
              fail("File \"" + x.getName + "\" was compiled correctly, although it contains errors!")
            catch
              case _ => println(x.getName + " passed")
      }
    }
