import java.io.File
import scala.io.Source
import org.scalatest._
import matchers.should._
import Inspectors._
import org.scalatest.flatspec.AnyFlatSpec
def readFile:String => Array[String] = name => Source.fromFile(name).getLines.toArray
class PositivesTest extends AnyFlatSpec with Matchers:
  val positives = new File("examples/correct/").listFiles
  forEvery(positives){
    x =>
      try
        new AST(readFile(x.getPath)) shouldNot be (null)
      catch
        case e => fail("File \"" + x.getName + "\" was not compiled correctly! Error: " + e.getMessage)
  }

class NegativesTest extends AnyFlatSpec with Matchers:
  val positives = new File("examples/wrong/").listFiles
  forEvery(positives){
    x =>
      try
        new AST(readFile(x.getPath)) shouldNot be (null)
        fail("File \"" + x.getName + "\" was compiled correctly, although it contains errors!")
      catch
        case _ =>
  }