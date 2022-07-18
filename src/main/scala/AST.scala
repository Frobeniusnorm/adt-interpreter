import scala.collection.immutable.HashSet
import scala.jdk.FunctionWrappers.RichFunction1AsDoubleToIntFunction
import scala.annotation.meta.param
import scala.collection.immutable.HashMap

object ASTFlags{
    var doColor = false
}

def stripString(str:String, line:Int):Option[String] = 
    val first = str.indexOf("\"")
    val last = str.lastIndexOf("\"")
    if first != -1 && first != last then
        //check if first and last only consists of seperators
        val stump = (if first > 1 then str.substring(1, first) else "") + 
                    (if last+1 < str.length then str.substring(last + 1) else "")
        if !stump.find(c => c != ' ' && c != '\t').isEmpty then
            throw new ParserException("illegal String: " + str, line)
        Some(str.substring(first + 1, last))
    else None

def stripList(str:String, line:Int):Option[List[String]] = 
    val first = str.indexOf("[")
    val last = str.lastIndexOf("]")
    if first != -1 && last != -1 then
        //get each List Element and convert it in a Cons and Nil concatenation
        val listcnt = str.substring(first + 1, last)
        if listcnt.isEmpty() then
            Some(List())
        else
            Some(listcnt.split(",").toList)
    else if (first == -1 || last != -1) && first != last then
        throw new ParserException("illegal String: " + str, line)
    else None

def stripComment(str:String) = 
    if str.contains("//") then
        str.split("//")(0)
    else str
def withoutSeperators(str:String) = str.replaceAll("[ \t]", "")
def stripNameFromSeperators(str:String, line:Int) = 
    val parts = str.split("[ \t]").filter(x => !x.isEmpty && x != " " && x != "\t")
    if(parts.length != 1) 
        throw new ParserException("illegal identifier: " + str, line)
    parts(0)
def splitAtFirst(str:String)(sep:Char) = 
    val idx = str.indexOf(sep)
    if idx == -1 then Array(str)
    else if idx == 0 then Array(str.substring(1))
    else if idx == str.length - 1 then Array(str.substring(0, str.length - 1))
    else Array(str.substring(0, idx), str.substring(idx + 1, str.length))

def countMatches(str:String, pattern:String) = 
    (str.length() - str.replace(pattern, "").length) / pattern.length

case class Type(tp:String, isGeneric:Boolean = false):
    override def toString:String = tp

abstract class Node
case class Program(adts:Array[ADT], expr:Array[Equation] = Array.empty[Equation], 
        constants:HashMap[String, Equation] = HashMap.empty[String,Equation]) extends Node:
    var orig_constants = constants

case class ADT(name:String, axs:Array[Axiom], ops:HashSet[Operation], sorts:HashSet[String]) extends Node:
    var typeVars:HashSet[String] = HashSet.empty[String]

case class Operation(name:String, var par:Array[Type], var ret:Type) extends Node:
    var orig_adt:String = "" //for namespaces: safes which adt it belongs to
    override def toString = name + "(" + (par.flatMap(t => Array(", ", t.tp)).drop(1).fold("")(_ + _)) + "):" + ret.tp 

abstract class Equation(val operation:String):
    def getVariables : HashMap[String, AtomEq]

case class AtomEq(op:String, var varType:Option[Type] = None, namespace : Option[String] = None) extends Equation(op):
    def makeTypedVar(typ:String) = AtomEq(operation, Some(new Type(typ)))
    var ref_op: Option[Operation] = None //for namespaces from Parser
    private var allowed_var = true
    def onlyAsOperation() = 
        allowed_var = false
        this
    def allowedAsVar() = allowed_var
    override def getVariables : HashMap[String, AtomEq] = if varType.isEmpty then HashMap.empty[String, AtomEq] else HashMap((op, this))
    override def toString() = 
        if varType.isEmpty then 
            (if ASTFlags.doColor then "\u001b[32m" else "") + operation + (if ASTFlags.doColor then "\u001b[0m" else "")
        else 
            (if ASTFlags.doColor then "\u001b[36m" else "") + operation + (if ASTFlags.doColor then "\u001b[0m" else "")

case class RecEq(op:String, params:Array[Equation], namespace : Option[String] = None) extends Equation(op):
    var ref_op : Option[Operation] = None //reference operation, needed for operation overloading and namespaces
    override def getVariables : HashMap[String, AtomEq] = params.foldLeft(HashMap.empty[String, AtomEq])((o, e) => o ++ e.getVariables)
    override def toString() = 
        (if ASTFlags.doColor then "\u001b[35m" else "") + operation + (if ASTFlags.doColor then "\u001b[0m" else "") + "(" + 
        params.zipWithIndex.map((x, i) => x.toString + (if i != params.length -1 then ", " else "")).fold("")(_+_) + ")"
//Conditional Equation
case class Condition(left:Equation, equals:Boolean, right:Equation):
    def getVariables = if left == null || right == null then 
        HashSet.empty[String]
        else HashSet.from(left.getVariables.keySet)

object Condition:
    val elseCond = Literal(new Condition(null, true, null))

abstract class LogicTerm:
    def getVariables : HashSet[String]
case class Literal(e:Condition) extends LogicTerm:
    override def getVariables = e.getVariables
case class Disjunction(parts:List[LogicTerm]) extends LogicTerm:
    override def getVariables = parts.foldLeft (HashSet.empty[String]) ((acc, x) => acc ++ x.getVariables)
case class Conjunction(parts:List[LogicTerm]) extends LogicTerm:
    override def getVariables = parts.foldLeft (HashSet.empty[String]) ((acc, x) => acc ++ x.getVariables)

//Case Equation: Equation -> and in first dimension, or in second dimension 
case class CaseEq(cases : Array[(Equation, LogicTerm)]) extends Equation(""):
    override def getVariables : HashMap[String, AtomEq] = cases.foldLeft(HashMap.empty[String, AtomEq])((o, e) => o ++ e._1.getVariables)

case class Axiom(left:Equation, right:Equation) extends Node:
    override def toString() = left.toString + (if ASTFlags.doColor then "\u001b[33m " else " ") + '=' + (if ASTFlags.doColor then "\u001b[0m " else " ") + right.toString

class AST(lines:Array[String]):
    LineTracker.clean()
    var constants:Option[HashMap[String, Equation]] = None
    val program = parse(lines map stripComment)
    //selects and groups the lines into adt groups, selects all other lines as to be evaluated expressions and parsed both
    def parse(lines:Array[String]):Program =
        val adts = lines.zipWithIndex
            .map((line, i) => if line.startsWith("adt ") || line.startsWith("end") then i else -1)
            .filter(_ != -1)
            
        if adts.length % 2 != 0 then
            throw new ParserException("Pairs of adts and ends do not match correctly!")
        val adtspaces = (adts grouped(2)).toList
        //lines in adts as hashset for contains performance
        val containedLines = HashSet.from((adtspaces flatMap (x => x(0) to x(1))))
        //lines that are not already in scope of a adt
        val unused = (0 until lines.length) filter(!containedLines.contains(_)) map(i => (i, lines(i)))
        //include stdlib?
        val stlibocc = unused filter (_._2 == "{use stdlib}")
        if stlibocc.size > 1 then throw new ParserException("More than one import of the stdlib will lead to name collisions", stlibocc(0)._1)
        val stdlib = 
            if stlibocc.size == 1 then
                StdLib.used = true
                StdLib.adts.map(x => parseADT(x.split("\n"), -1))
            else
                StdLib.used = false
                Array.empty[ADT]

        val eqlines = unused filter(x => !withoutSeperators(x._2).isEmpty && x._2 != "{use stdlib}")
        constants = Some(HashMap.from((eqlines filter(_._2.contains(":=")) map (pel => parseConstant(pel._2, pel._1))).toArray))
        new Program(adtspaces.map(arr => parseADT(lines slice(arr(0), arr(1)), arr(0))).toArray ++ stdlib, 
                    (eqlines filter(!_._2.contains(":=")) map (pel => parseEq(pel._2, pel._1))).toArray,
                    constants.get)
    
    //Parses an ADT by its lines and subelements (sorts, ops, axs) by selecting the corresponding lines and calling their parse operations
    def parseADT(lines:Array[String], starts:Int):ADT =
        val name = 
            if !lines.isEmpty then
                val parts = lines(0).split(" ")
                if lines(0).startsWith("adt ") && parts.length == 2 then
                parts(1)  
                else throw new ParserException("Illegal adt name: " + lines(0), if starts == -1 then -1 else starts)
            else throw new ParserException("Empty ADTs are not allowed", if starts == -1 then -1 else starts)
        if LineTracker.containsKey("adt(" + name + ")") then 
            throw new ParserException(s"adt \"${name}\" was declared multiple times", if starts == -1 then -1 else starts)
        val sorts = 
            val sortlines_wi = lines.zipWithIndex.filter(_._1.startsWith("sorts "))
            val sortlines = sortlines_wi map (_._1)
            if(sortlines.length > 1) throw new ParserException("Too many sort statements for one datatype!", if starts == -1 then -1 else sortlines_wi(1)._2 + starts)
            if(sortlines.length < 1) throw new ParserException("Every Datatype needs one sorts-statement, because it must at least sort itself!", starts)
            if(sortlines(0).length < 7) throw new ParserException("A Datatype must at least sort itself!", if starts == -1 then -1 else sortlines_wi(0)._2 + starts)
            LineTracker.registerLine("sorts(" + name + ")", if starts == -1 then -1 else sortlines_wi(0)._2 + starts)
            sortlines(0).substring(6).split(",").map(x => 
                stripNameFromSeperators(x, if starts == -1 then -1 else sortlines_wi(0)._2 + starts))
        val ops = 
            val opslines = lines.zipWithIndex.filter((x, i) => x.startsWith("ops"))
            if(opslines.length == 0) throw new ParserException("Datatypes need an operations part, even if it may be empty", starts)
            if(opslines.length > 1) throw new ParserException("Only one operations part is allowed per datatype!", if starts == -1 then -1 else opslines(1)._2 + starts)
            if(opslines(0)._1.length != 3) throw new ParserException("Illegal characters after ops: " + opslines(0)._1, opslines(0)._2)
            val start = opslines(0)._2
            LineTracker.registerLine("ops(" + name + ")", if starts == -1 then -1 else starts + start)
            val sortsline = LineTracker.getLine("sorts(" + name + ")")
            if starts + start < sortsline then throw new ParserException("operations part must be declared AFTER sorts part", if starts == -1 then -1 else starts + start)
            val term_cand = lines.zipWithIndex.filter((x, i) => x.startsWith("axs")).map(_._2)
            val term = if term_cand.length >= 1 then term_cand(0) else lines.length
            if term < start then 
                throw new ParserException("axiom part must be declared AFTER operations part", if starts == -1 then -1 else term + starts)
            lines.slice(start + 1, term).zipWithIndex.filter(l => !withoutSeperators(l._1).isEmpty).map(l => parseOP(l._1, if starts == -1 then -1 else l._2 + start + 1 + starts))
            
        ops foreach(op => op.orig_adt = name)
        val axs = 
            val axslines = lines.zipWithIndex.filter((x, i) => x.startsWith("axs"))
            if axslines.length == 0 then Array[Axiom]()
            else
                if(axslines.length > 1) throw new ParserException("Only one axiom part is allowed per datatype!", if starts == -1 then -1 else axslines(1)._2 + starts)
                if(axslines(0)._1.length != 3) throw new ParserException("Illegal characters after axs: " + axslines(0)._1, if starts == -1 then -1 else axslines(0)._2 + starts)
                val start = axslines(0)._2
                LineTracker.registerLine("axs(" + name + ")", if starts == -1 then -1 else start + starts)
                val nspace = lines.slice(start + 1, lines.length)
                nspace.zipWithIndex map((x,i) => parseAx(i, nspace, if starts == -1 then -1 else start + 1 + starts)) filter(!_.isEmpty) map(_.get)

        LineTracker.registerLine("adt(" + name + ")", if starts == -1 then -1 else starts)
        new ADT(name, axs, HashSet[Operation]() ++ ops, new HashSet[String]() ++ sorts)
    
    def parseConstant(line:String, linenb:Int):(String, Equation) = 
        val parts = line.split(":=") 
        if(parts.length > 2) throw new ParserException("Per constant definition only one ':=' is allowed!", linenb)
        if(parts.length < 2) throw new ParserException("Unexpected number of sides for constant definition!", linenb)
        val left = stripNameFromSeperators(parts(0), linenb)
        LineTracker.registerLine(s"const(${left})", linenb)
        (left, parseEq(parts(1), linenb))

    //Parses one Operation in one line
    def parseOP(line:String, linenb:Int):Operation =
        val parts1 = line.split(":")
        if(parts1.length != 2) throw new ParserException(s"illegal operation definition: \"${line}\"", linenb)
        val name = stripNameFromSeperators(parts1(0), linenb)
        val pars = parts1(1)
        val arrowpos = pars.indexOf("->")
        if(arrowpos == -1 || line.length < arrowpos + 3) throw new TypeException("Every Operation needs a return type!", linenb)
        val ret = new Type(stripNameFromSeperators(pars.substring(arrowpos + 2), linenb))
        val paramspace = pars.substring(0, arrowpos)
        
        val par = if paramspace.replaceAll(" ", "").replaceAll("\t", "").length > 0 then 
                paramspace.split(" x ").map(x => new Type(stripNameFromSeperators(x, linenb)))
                else Array[Type]()
        val nmbx = countMatches(paramspace, " x ")
        if par.length != nmbx + 1 && !(par.length == 0 && nmbx == 0) then throw new ParserException("Unexpected number of Occurences of ' x ' in parameters ("+nmbx+" occurences, " +par.length + " parameters)!", linenb)
        val op = new Operation(name, par, ret)
        LineTracker.registerLine(s"op(${op})", linenb)
        op

    //parses one Axiom in one line, but the axiom may consume multiple lines if it has a case statement in the right equation, in this case all the lines that are consumed by the axiom will yield None
    def parseAx(index:Int, lines:Array[String], starts:Int):Option[Axiom] = 
        val line = lines(index)
        if line == null || (withoutSeperators(line)).isEmpty then None //has already been consumed
        else
            val parts = splitAtFirst(line)('=')
            if(parts.length != 2) 
                throw new ParserException("An Axiom is always an equation with a left hand and right hand side sperated by a '='! "
                    , if starts == -1 then -1 else index + starts)
            val axs = if withoutSeperators(parts(1)) startsWith("|") then
                //yeay pain
                val csl = lines.drop(index + 1).zipWithIndex takeWhile(l => 
                    withoutSeperators(l._1) startsWith("|")
                )
                csl foreach (l => lines(l._2 + index + 1) = null)
                new Axiom(parseEq(parts(0), if starts == -1 then -1 else index + starts), 
                            parseCaseEq(Array(parts(1)) ++ (csl map (_._1)), if starts == -1 then -1 else index + starts))
            else new Axiom(parseEq(parts(0), if starts == -1 then -1 else index + starts), 
                        parseEq(parts(1), if starts == -1 then -1 else index + starts))
            LineTracker.registerLine("axseq(" + axs.left + ")", if starts == -1 then -1 else index + starts)
            Some(axs)

    def stripConstants(line:Equation, const:HashMap[String, Equation], linenb:Int):Equation = line match 
        case AtomEq(op, vt, ns) =>
            if const.contains(op) then stripConstants(const(op), const, linenb)
            else line
        case RecEq(op, pars, ns) =>
            if const.contains(op) then throw new ParserException("Constants are not allowed in function calls!", linenb)
            val res = new RecEq(op, pars map(stripConstants(_, const, linenb)), ns)
            res.ref_op = (line.asInstanceOf[RecEq]).ref_op
            res
        case CaseEq(cases) => new CaseEq(cases map (ce => (stripConstants(ce._1, const, linenb), stripConstants(ce._2, const, linenb))))
    
    def stripConstants(line:LogicTerm, const:HashMap[String, Equation], linenb:Int):LogicTerm = line match 
        case Literal(cond) => 
            if cond == Condition.elseCond then line
            else 
                Literal(Condition(stripConstants(cond.left, const, linenb), cond.equals, stripConstants(cond.right, const, linenb)))
        case Disjunction(terms) => Disjunction(terms map (stripConstants(_, const, linenb)))
        case Conjunction(terms) => Disjunction(terms map (stripConstants(_, const, linenb)))

    //parses one Equation in one line
    def parseEq(line:String, linenb:Int = -1):Equation =
        //extracts only the operation for the outer most brackets and leaves the other ones as strings
        if line.contains(":=") then throw new ParserException("Constant definitions are only allowed on the global scope!", linenb)
        def splitFlatParamSpace(str:String):Array[String] = 
            //two types of brackets: (), []
            val flr = str.foldLeft((0, 0, List[String]("")))((acc, x) => 
                (if x == '(' then acc._1 + 1 else if x == ')' then acc._1 - 1 else acc._1,
                 if x == '[' then acc._2 + 1 else if x == ']' then acc._2 - 1 else acc._2,
                if x == ',' && acc._1 == 0 && acc._2 == 0 then "" :: acc._3 else (acc._3.head + x) :: acc._3.tail)    
            )
            if flr._1 != 0 || flr._2 != 0 then throw new ParserException("mismatched brackets", linenb)
            else flr._3.reverse.toArray
        def nameAndNamespace(name:String):(String, Option[String]) =
            val res = stripNameFromSeperators(name, linenb)
            if res.contains(".") then
                val parts = res.split("\\.")
                if parts.length != 2 then
                    throw new ParserException("Invalid namespace decleration (\"" + name + "\")!", linenb)
                (parts(1), Some(parts(0)))
            else (res, None)
        def genString(str:List[Char]):Equation = str match
            case Nil => new AtomEq("Nil", Some(Type("List", false)))
            case h::t => new RecEq("Cons", Array(new AtomEq(s"'${h}'", Some(Type("Char"))), genString(t)), None)
        def genNat(number:Int):Equation = number match
            case 0 => new AtomEq("zero", Some(Type("Nat")), None)
            case x => new RecEq("succ", Array(genNat(x-1)), None)
        def genList(els:List[String]):Equation = els match
            case Nil => new AtomEq("Nil", Some(Type("List", false)))
            case h::t => new RecEq("Cons", Array(parseEq(h, linenb), genList(t)))
        def helperPEQ = 
            val opening = line.indexOf('(')
            val closing = line.lastIndexOf(')')
            if opening == -1 && closing == -1 then 
                lazy val possstr = stripString(line, linenb)
                lazy val posslst = stripList(line, linenb)
                if StdLib.used && !possstr.isEmpty then
                    new RecEq("fromList", Array(genString(possstr.get.toCharArray.toList)), None)
                else if StdLib.used && !posslst.isEmpty then
                    genList(posslst.get)         
                else
                    val (identifier, namespace) = nameAndNamespace(line)
                    if StdLib.used && (identifier.toCharArray filter (digit => digit < '0' || digit > '9')).isEmpty then
                        val number = identifier.toInt
                        genNat(number)
                    else
                        if !constants.isEmpty && constants.get.contains(identifier) then 
                            stripConstants(constants.get(identifier), constants.get, linenb)
                        else AtomEq(identifier, None, namespace)
            else if opening == -1 || closing == -1 then
                throw new ParserException("mismatched brackets" + line, linenb)
            else if closing == opening + 1 then
                val (identifier, namespace) = nameAndNamespace(line.substring(0, opening))
                if !constants.isEmpty && constants.get.contains(identifier) then 
                    stripConstants(constants.get(identifier), constants.get, linenb)
                else AtomEq(identifier, None, namespace).onlyAsOperation()
            else
                val paramspace = line.substring(opening + 1, closing)
                val (identifier, namespace) = nameAndNamespace(line.substring(0, opening))
                if !paramspace.contains(",") then
                    RecEq(identifier, Array(parseEq(paramspace, linenb)), namespace)
                else
                    RecEq(identifier, splitFlatParamSpace(paramspace).map(pss => parseEq(pss, linenb)), namespace)
        val reseq = helperPEQ
        LineTracker.registerLine(s"eq(${reseq})", linenb)
        reseq
                
    def parseCaseEq(lines:Array[String], linenb:Int = -1):CaseEq =
        new CaseEq(lines.map (l => 
            val cIf = l.contains(" if ")
            val cEl = l.contains(" else")
            if cIf && cEl then throw new ParserException("per case only one 'if' OR 'else' is allowed, not both!", linenb)
            if !cIf && !cEl then throw new ParserException("per case one 'if' or 'else' is expected!", linenb)
            if cIf then
                val ecP = l.split(" if ")
                if ecP.length != 2 then throw new ParserException("Only one 'if' per case allowed!", linenb)
                (parseEq(ecP(0).replaceFirst("\\|", ""), linenb), parseLogicTerm(ecP(1), linenb))
            else
                val ecP = l.replace("else", "").replaceFirst("\\|", "")
                (parseEq(ecP, linenb), Condition.elseCond)
        ))
    //ands and ors, yes i love them
    //example (a | b | c) & d & (e | f) | g = Conjunction(Disjunction(a,b,c), d, Disjunction(e, f))
    def parseLogicTerm(line:String, linenb:Int = -1):LogicTerm =
        if !line.contains("&") && !line.contains("|") then
            Literal(parseCondition(line, linenb))
        else
            def splitFlat(str:String)(c:Char) = str.foldLeft((List[String](""), 0, false))((curr, x) => 
                val withchar = if x != ' ' && x != '\t' then (x + curr._1.head) :: curr._1.tail else curr._1
                if x == '(' then 
                    if curr._2 == 0 then
                        if curr._1.head.isEmpty then
                            (curr._1, curr._2 + 1, false)
                        else (withchar, curr._2 + 1, true) //this is a function call, dont kill the bracket
                    else (withchar, curr._2 + 1, curr._3)
                else if x == ')' then 
                    if curr._2 == 1 then 
                        if curr._3 then 
                            (withchar, curr._2 - 1, false) //this is a function call, dont kill the bracket
                        else (curr._1, curr._2 - 1, false)
                    else (withchar, curr._2 - 1, curr._3)
                else if curr._2 == 0 && x == c then ("" :: curr._1, curr._2, false)
                else (withchar, curr._2, curr._3)
            )
            //first try to collect all the disjunctive terms
            val disj = splitFlat(line)('|')
            if disj._2 != 0 then throw new ParserException("mismatched brackets!", linenb)
            if disj._1.length == 1 then 
                val conj = splitFlat(line)('&')
                Conjunction(conj._1.reverse map(x => parseLogicTerm(x.reverse, linenb)))
            else Disjunction(disj._1.reverse map(x => parseLogicTerm(x.reverse, linenb)))

    def parseCondition(line:String, linenb:Int = -1):Condition = 
        if line.contains("!=") then 
            val cP = line.split("!=")
            if cP.length != 2 then throw new ParserException("Only exact one '=' or '!=' with one left and one right side per condition is allowed!", linenb)
            new Condition(parseEq(cP(0), linenb), false, parseEq(cP(1), linenb))
        else
            val cP = line.split("=")
            if cP.length != 2 then throw new ParserException("Only exact one '=' or '!=' with one left and one right side per condition is allowed!", linenb)
            new Condition(parseEq(cP(0), linenb), true, parseEq(cP(1), linenb))
