import scala.collection.immutable.HashSet
import scala.jdk.FunctionWrappers.RichFunction1AsDoubleToIntFunction
import scala.annotation.meta.param
import scala.collection.immutable.HashMap

def withoutSeperators(str:String) = str.replaceAll("[ \t]", "")
def stripNameFromSeperators(str:String) = 
    val parts = str.split("[ \t]").filter(x => !x.isEmpty && x != " " && x != "\t")
    if(parts.length != 1) throw new RuntimeException("illegal identifier: " + str)
    parts(0)


abstract class Node
case class Program(adts:Array[ADT], expr:Array[Equation] = Array.empty[Equation]) extends Node

case class ADT(name:String, axs:Array[Axiom], ops:HashSet[Operation], sorts:HashSet[String]) extends Node

case class Operation(name:String, par:Array[String], ret:String) extends Node

abstract class Equation(val operation:String):
    def getVariables : HashMap[String, AtomEq]
case class AtomEq(op:String, varType:Option[String] = None) extends Equation(op):
    def makeTypedVar(typ:String) = AtomEq(operation, Some(typ))
    override def getVariables : HashMap[String, AtomEq] = if varType.isEmpty then HashMap.empty[String, AtomEq] else HashMap((op, this))
    override def toString() = operation

case class RecEq(op:String, params:Array[Equation]) extends Equation(op):
    override def getVariables : HashMap[String, AtomEq] = params.foldLeft(HashMap.empty[String, AtomEq])((o, e) => o ++ e.getVariables)
    override def toString() = operation + "(" + params.zipWithIndex.map((x, i) => x.toString + (if i != params.length -1 then ", " else "")).fold("")(_+_) + ")"
case class Axiom(left:Equation, right:Equation) extends Node:
    override def toString() = left.toString + " = " + right.toString

class AST(lines:Array[String]):
    val program = parse(lines)
    def parse(lines:Array[String]):Program =
        val adts = lines.zipWithIndex
            .map((line, i) => if line.startsWith("adt ") || line.startsWith("end") then i else -1)
            .filter(_ != -1)
            
        if adts.length % 2 != 0 then
            throw new RuntimeException("Pairs of adts and ends do not match correctly!")
        val adtspaces = (adts grouped(2)).toList
        //lines in adts as hashset for contains performance
        val containedLines = HashSet.from((adtspaces flatMap (x => x(0) to x(1))))
        //lines that are not already in scope of a adt
        val eqlines = (0 until lines.length) filter(!containedLines.contains(_)) map(i => lines(i)) filter(!withoutSeperators(_).isEmpty)
        new Program(adtspaces.map(arr => parseADT(lines slice(arr(0), arr(1)))).toArray, (eqlines map parseEq).toArray)

    def parseADT(lines:Array[String]):ADT =
        val name = 
            if !lines.isEmpty then
                val parts = lines(0).split(" ")
                if lines(0).startsWith("adt ") && parts.length == 2 then
                  parts(1)  
                else throw new RuntimeException("Could not parse line, illegal adt name: " + lines(0))
            else throw new RuntimeException("Empty ADTs are not allowed")
        val sorts = 
            val sortlines = lines.filter(_.startsWith("sorts "))
            if(sortlines.length > 1) throw new RuntimeException("Too many sort statements for one datatype!")
            if(sortlines.length < 1) throw new RuntimeException("Every Datatype needs one sorts-statement, because it must at least sort itself!")
            if(sortlines(0).length < 7) throw new RuntimeException("A Datatype must at least sort itself!")
            sortlines(0).substring(6).split(",").map(x => 
                stripNameFromSeperators(x))
        val ops = 
            val opslines = lines.zipWithIndex.filter((x, i) => x.startsWith("ops"))
            if(opslines.length == 0) throw new RuntimeException("Datatypes need an operations part, even if it may be empty")
            if(opslines.length > 1) throw new RuntimeException("Only one operations part is allowed per datatype!")
            if(opslines(0)._1.length != 3) throw new RuntimeException("Illegal characters after ops: " + opslines(0)._1)
            val start = opslines(0)._2
            val term = lines.zipWithIndex.filter((x, i) => (x.startsWith("end") || x.startsWith("axs")) && i > start).map(_._2).min
            lines.slice(start + 1, term).map(parseOP)
        val axs = 
            val axslines = lines.zipWithIndex.filter((x, i) => x.startsWith("axs"))
            if axslines.length == 0 then Array[Axiom]()
            else
                if(axslines.length > 1) throw new RuntimeException("Only one axiom part is allowed per datatype!")
                if(axslines(0)._1.length != 3) throw new RuntimeException("Illegal characters after axs: " + axslines(0)._1)
                val start = axslines(0)._2
                lines.slice(start + 1, lines.length).map(parseAx)
        new ADT(name, axs, HashSet[Operation]() ++ ops, new HashSet[String]() ++ sorts)
    

    def parseOP(line:String):Operation =
        val parts1 = line.split(":")
        if(parts1.length != 2) throw new RuntimeException("illegal operation definition: " + line)
        val name = stripNameFromSeperators(parts1(0))
        val pars = parts1(1)
        val arrowpos = pars.indexOf("->")
        if(arrowpos == -1 || line.length < arrowpos + 3) throw new RuntimeException("Every Operation needs a return type! In: " + line)
        val ret = stripNameFromSeperators(pars.substring(arrowpos + 2))
        val paramspace = pars.substring(0, arrowpos)
        
        val par = if paramspace.replaceAll(" ", "").replaceAll("\t", "").length > 0 then 
            paramspace.split(" x ").map(stripNameFromSeperators)
        else Array[String]()
        new Operation(name, par, ret)

    def parseAx(line:String):Axiom = 
        val parts = line.split("=")
        if(parts.length != 2) throw new RuntimeException("An Axiom is always an equation with a left hand and right hand side sperated by a semicolon!")
        new Axiom(parseEq(parts(0)), parseEq(parts(1)))

    def parseEq(line:String):Equation =
        def splitFlatParamSpace(str:String):Array[String] = 
            val flr = str.foldLeft((0, List[String]("")))((acc, x) => 
                (if x == '(' then acc._1 + 1 else if x == ')' then acc._1 - 1 else acc._1,
                 if x == ',' && acc._1 == 0 then "" :: acc._2 else (acc._2.head + x) :: acc._2.tail)    
            )
            if flr._1 != 0 then throw new RuntimeException("mismatched brackets")
            else flr._2.reverse.toArray

        val opening = line.indexOf('(')
        val closing = line.lastIndexOf(')')
        if opening == -1 && closing == -1 then 
            AtomEq(stripNameFromSeperators(line))
        else if opening == -1 || closing == -1 then
            throw new RuntimeException("mismatched brackets: " + line)
        else if closing == opening + 1 then
            AtomEq(stripNameFromSeperators(line.substring(0, opening)))
        else
            val paramspace = line.substring(opening + 1, closing)
            if !paramspace.contains(",") then
                RecEq(stripNameFromSeperators(line.substring(0, opening)), Array(parseEq(paramspace)))
            else
                RecEq(stripNameFromSeperators(line.substring(0, opening)), splitFlatParamSpace(paramspace).map(parseEq))






