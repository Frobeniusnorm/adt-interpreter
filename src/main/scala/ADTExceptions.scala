import scala.collection.mutable.HashMap
class CompilerException(msg:String, line:Int) extends RuntimeException(msg):
    override def getMessage() = (if line >= 0 then "[In line: " + (line + 1) + "] " else "") + msg
    
class ParserException(msg:String, line:Int = -1) extends CompilerException(msg, line)
class TypeException(msg:String, line:Int = -1) extends CompilerException(msg, line)
class ExecutionException(msg:String, line:Int = -1) extends CompilerException(msg, line)
class InfiniteRecursionException(msg:String, line:Int = -1) extends ExecutionException(msg, line)

object LineTracker:
    private val lineTable:HashMap[String, Int] = HashMap.empty[String, Int]
    def registerLine(key:String, line:Int) = 
        lineTable += ((key, line))
    def getLine(key:String) = 
        if lineTable.contains(key) then lineTable(key) else -1
    def containsKey(key:String) = lineTable.contains(key)
    def clean() = lineTable.clear