import scala.collection.mutable.HashMap
class CompilerException(msg:String, line:Int) extends RuntimeException(msg):
    override def getMessage() = (if line >= 0 then "[In line: " + (line + 1) + "] " else "") + msg
    
class ParserException(msg:String, line:Int = -1) extends CompilerException(msg, line)
class TypeException(msg:String, line:Int = -1) extends CompilerException(msg, line)
class ExecutionException(msg:String, line:Int = -1) extends CompilerException(msg, line)

object LineTracker:
    private val lineTable:HashMap[String, Int] = HashMap.empty[String, Int]
    def registerLine(key:String, line:Int) = 
        lineTable += ((key, line))
    def getLine(key:String) = lineTable(key)