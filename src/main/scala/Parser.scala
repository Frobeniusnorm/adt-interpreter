import scala.collection.immutable.HashMap
import scala.collection.immutable.HashSet

object Parser:

    def parseProgram(prog:Program):Program = 
        val namespaces:HashMap[String, HashSet[Operation]] = HashMap.from(prog.adts map(x => x.name -> x.ops))
        val adts = HashMap.from(prog.adts map(x => x.name -> x))
        //helper functions:
        /**
         * Checks if all used types appear in sorts
         */ 
        def checkNames(adt:ADT) = 
            //all types that are not contained in namespaces -> local generics that may be used
            val knownTypes = HashSet.from(namespaces filter(x => adt.sorts contains(x._1)) map(x => x._1))
            val typeVars = adt.sorts filter (!knownTypes.contains(_))
            //check operation names        
            for op <- adt.ops do
                for t <- op.par :+ op.ret do
                    if !(knownTypes contains (t.tp)) && !(typeVars contains (t.tp)) then 
                        throw new TypeException("Unknown Type \"" + t + "\" in ops of \"" + adt.name + "\"", LineTracker.getLine(s"op(${op})"))
                op.par = op.par map(par => if typeVars contains (par.tp) then Type(par.tp, true) else par)
                op.ret = if typeVars contains (op.ret.tp) then Type(op.ret.tp, true) else op.ret
            adt.typeVars = HashSet.from(typeVars)
        
        /**
         * Checks types of all axioms of an adt and sets the variable types
         */ 
        def checkAndUpdateTypes(adt:ADT):ADT =
            
            val knownOps = HashMap.from((namespaces filter(x => adt.sorts contains(x._1)) flatMap(x => x._2)).toArray groupBy(x => x.name))
            val axs = adt.axs map (x => 
                val currentLine = LineTracker.getLine(s"axseq(${x.left})")
                val left = checkAndUpdateEquationType(knownOps, currentLine)(x.left)
                left match
                    case AtomEq(name, None, _) => throw new ParserException("Illegal atomic operation \"" + name + "\" on left hand side!", currentLine)
                    case AtomEq(name, Some(_), _) => throw new ParserException("Illegal single variable \"" + name + "\" on left hand side!", currentLine)
                    case CaseEq(cases) => throw new ParserException("Illegal case statement on left hand side of Axiom!", currentLine)
                    case _ => //that's fine
                val leftvars = left.getVariables
                val rightc = checkAndUpdateEquationType(knownOps, currentLine)(x.right, leftvars)
                val right = rightc match
                    case AtomEq(name, Some(_), ns) => left match
                        case lt:RecEq => 
                            AtomEq(name, Some(lt.ref_op.get.ret), ns) 
                    case CaseEq(cases) => CaseEq(cases map (cs => (cs._1 match //in case of a case equation, type all single variables that occur as cases
                        case AtomEq(name, Some(_), ns) => left match
                            case lt:RecEq => AtomEq(name, Some(lt.ref_op.get.ret), ns)
                        case umc => umc
                    , cs._2)))
                    case e => e
                
                //vars must match
                right.getVariables foreach((v1, ae1) =>
                    if !leftvars.contains(v1) then
                        throw new ParserException("Unknown Variable \"" + v1 + "\" on right hand side of Axiom!", currentLine)
                    val ae2 = leftvars(v1)
                    if ae1.varType.isEmpty then
                        throw new ParserException("Variable on right hand side has no type (wtf)!", currentLine)
                    if ae2.varType.isEmpty then
                        throw new ParserException("Variable on left hand side has no type (wtf)!", currentLine)
                    if ae1.varType.get != ae2.varType.get then
                        throw new TypeException("Could not match variable type for \"" + v1 + "\"! " +
                          "Type of variable on left hand side: \"" + ae2.varType.get + "\", on right hand side: \"" + ae1.varType.get + "\"", currentLine)
                )
                //still have to check if term variables even exist and type them
                val fright = right match
                    case CaseEq(cases) => 
                        def completeVars(eq:Equation):Equation = eq match
                            case null => null
                            case AtomEq(name, _, ns) => if leftvars.contains(name) then 
                                AtomEq(name, leftvars(name).varType, ns)
                                else if knownOps.contains(name) then
                                    AtomEq(name, None, ns)
                                else throw new ParserException("Unknown literal \"" + name + "\" in case condition!" , currentLine)
                            case tlre:RecEq =>
                                val (name, parts) = (tlre.op, tlre.params)
                                if !(knownOps contains name) then throw new ParserException("Could not find operation \"" + name + "\"!",currentLine) 
                                val foo = RecEq(name, (parts zip tlre.ref_op.get.par) map (p => 
                                    val rp = completeVars(p._1)
                                    val rpt = rp match 
                                        case AtomEq(namer, Some(t), _) => t
                                        case AtomEq(namer, None, ns) => ns match
                                            case None => knownOps(namer)(0).ret //assured trough typing method
                                            case Some(ns2) => 
                                                val poss = knownOps(namer) filter(op => op.orig_adt == ns2)
                                                if poss.length != 1 then throw new TypeException("Ambiguous usage of operation \"" + namer + "\"!", currentLine)
                                                poss(0)
                                        case rptc:RecEq => rptc.ref_op.get.ret
                                        case CaseEq(_) => throw new ParserException("Case Equations are not allowed to be recursively stacked!", currentLine)
                                    if rpt != p._2 then throw new TypeException("Could not match type \"" + rpt + "\" with expected type \"" +p._2+ "\" in operation \"" + name + "\"", currentLine)
                                    rp    
                                ), tlre.namespace)
                                foo.ref_op = tlre.ref_op
                                foo
                            case _ => throw new ParserException("Illegal Equation type in Condition: \"" + eq + "\"", currentLine)
                        def completeTerms(lt:LogicTerm):LogicTerm = lt match
                            case Literal(Condition(x, e, y)) => Literal(Condition(completeVars(x), e, completeVars(y)))
                            case Conjunction(parts) => Conjunction(parts map completeTerms)
                            case Disjunction(parts) => Disjunction(parts map completeTerms)
                        CaseEq(cases map(ce => (ce._1, completeTerms(ce._2))))
                    case diff => diff
                //left and right term must have same type
                val lefttype = left match
                    case lt:RecEq => lt.ref_op.get.ret
                val righttype = 
                    def getTypeOfBasic(e:Equation) = e match 
                        case AtomEq(name, Some(t), _) => t
                        case AtomEq(name, _, _) => knownOps(name)(0).ret //assured trough typing method
                        case rt:RecEq => rt.ref_op.get.ret
                    right match
                        case CaseEq(cases) => 
                            val firsttype= getTypeOfBasic(cases(0)._1)
                            if !cases.drop(1).forall(ce => getTypeOfBasic(ce._1) == firsttype) then
                                throw new TypeException("All results of cases must have same Type!", currentLine)
                            firsttype
                        case e:Equation => getTypeOfBasic(e)
                if(lefttype != righttype)
                    throw new TypeException("Type of left side (\"" + lefttype +"\") does not match type of right side (\"" + righttype +"\")! ",currentLine)
                new Axiom(left, fright)
            )
            new ADT(adt.name, axs, adt.ops, adt.sorts)
        //Every Equation must be typable, since it only has one outer operation
        /** Updates AtomicEq that are variables and checks if the type of the equation is complete */ 
        def checkAndUpdateEquationType(ops:HashMap[String, Array[Operation]], currentLine:Int)
                (eq:Equation, alreadydefvars:HashMap[String, AtomEq] = HashMap.empty[String, AtomEq]) : Equation = 
            eq match
                case AtomEq(name, _, ns) => if ops.contains(name) then AtomEq(name, None, ns) else 
                        if !(eq.asInstanceOf[AtomEq]).allowedAsVar() then 
                            throw new ParserException(s"The identifier \"${name}()\" cannot be used as a variable", currentLine)
                        AtomEq(name, Some(Type("", false)), ns)
                case RecEq(name, e:Array[Equation], ns) =>
                    if !(ops contains name) then throw new ParserException("Unknown Operation \"" + name + "\"", currentLine)
                    val op_cand = ops(name)
                    if op_cand.length == 1 then
                        val op = op_cand(0)
                        if op.par.length != e.length then throw new TypeException("Not enough parameters for operation \"" + name + "\"", currentLine)
                        var alrdTyped = HashMap.empty[String, Type] //maps generics to actual types (should only happen during equation evaluation)
                        val np = 
                            for zeqp <- (op.par zip e) yield
                                val sep = checkAndUpdateEquationType(ops, currentLine)(zeqp._2, alreadydefvars)
                                sep match
                                    case AtomEq(n2, Some(_), ns2) => 
                                        AtomEq(n2, Some(zeqp._1), ns2)
                                    case _ =>
                                        val ttp = sep match 
                                            case nsep:RecEq => nsep.ref_op.get.ret
                                            case AtomEq(n2, None, _) => 
                                                val aecand = ops(n2)
                                                if aecand.length != 1 then throw new TypeException("Ambiguous operation definitions for operation \"" + n2 + "\" with no parameters!", currentLine)
                                                aecand(0).ret
                                        val tt = if alrdTyped.contains(ttp.tp) then alrdTyped(ttp.tp)
                                            else 
                                                if zeqp._1.isGeneric && !ttp.isGeneric then
                                                    if !(alrdTyped contains(zeqp._1.tp)) then
                                                        alrdTyped = alrdTyped + ((zeqp._1.tp, ttp))
                                                ttp
                                        val z1tt = if alrdTyped.contains(zeqp._1.tp) then alrdTyped(zeqp._1.tp) else zeqp._1
                                        if !(ops contains sep.operation) || (!(tt equals zeqp._1) && !(tt equals z1tt)) then
                                            throw new TypeException("Could not match \"" + sep.operation + "\" (with type: \"" + tt + "\") with expected type \"" + z1tt + "\" in operation call for \"" + name + "\"", currentLine)
                                        sep
                        val nre = new RecEq(name, np)
                        nre.ref_op = Some(op)
                        nre
                    else //multiple overriden candidates smh
                        def calcParType:Equation => Type = x => x match 
                            case n2:RecEq => n2.ref_op.get.ret
                            case ae:AtomEq =>
                                val n2 = ae.op
                                val poss = 
                                    if !ae.namespace.isEmpty then
                                        ops(n2) filter (op => op.orig_adt == ae.namespace.get)
                                    else ops(n2)
                                if poss.length > 1 then throw new TypeException("Ambiguous operation definitions for operation \"" + n2 + "\" with no parameters!", currentLine)
                                if poss.length == 0 then throw new TypeException("No fitting operation found for \"" + n2 + "\"" + 
                                    (if !ae.namespace.isEmpty then " with namespace \"" +ae.namespace.get+ "\"!" else "!"), currentLine) 
                                poss(0).ret
                            case _ => null 
                        
                        val pass1pars = e map (checkAndUpdateEquationType(ops, currentLine)(_, alreadydefvars))
                        val partypes = pass1pars map (xeq => xeq match
                            case AtomEq(n2, Some(_), _) =>
                                if alreadydefvars contains(n2) then
                                    alreadydefvars(n2) match
                                        case AtomEq(_, Some(t), _) => t
                                        case _ => calcParType(xeq)
                                else null
                            case _ => calcParType(xeq))
    
                        val actual_cand = 
                            val fe = op_cand filter(oc => oc.par.length == partypes.length 
                                            && oc.par.zip(partypes).forall(p => p._2 == null || p._1 == p._2 || p._1.isGeneric))
                            if !ns.isEmpty then
                                fe filter (op => op.orig_adt == ns.get)
                            else fe
                        if actual_cand.length > 1 then throw new TypeException("Ambiguous operation usage for operation \"" + name + "\"", currentLine)
                        if actual_cand.length == 0 then throw new TypeException("No fitting definition for operation \"" + name + "\"", currentLine)
                        val actual = actual_cand(0)
                        val pass2pars = (pass1pars zip actual.par) map (x => x._1 match
                            case AtomEq(n2, Some(_), ns) => AtomEq(n2, Some(x._2), ns)
                            case AtomEq(n2, None, ns) => 
                                if ops(n2)(0).ret != x._2 then 
                                    new TypeException("Could not match \"" + n2 + "\" with expected type \"" + x._2 + "\" in operation call for \"" + name + "\"", currentLine)
                                x._1
                            case nsep:RecEq => 
                                if nsep.ref_op.get.ret != x._2 then
                                    new TypeException("Could not match \"" + nsep.operation + "\" with expected type \"" + x._2 + "\" in operation call for \"" + name + "\"", currentLine)
                                x._1
                        )
                        val nre = new RecEq(name, pass2pars)
                        nre.ref_op = Some(actual)
                        nre
                case CaseEq(css) => 
                    def checkAndTypeLogicTerm(lt:LogicTerm) : LogicTerm = 
                        lt match
                            case Literal(cond) => Literal(checkAndTypeCondition(cond))
                            case Disjunction(parts) => Disjunction(parts map checkAndTypeLogicTerm)
                            case Conjunction(parts) => Conjunction(parts map checkAndTypeLogicTerm)
                    def checkAndTypeCondition(c:Condition) : Condition = c match
                        case Condition(null, true, null) => c
                        case Condition(l, op, r) => 
                            Condition(checkAndUpdateEquationType(ops, currentLine)(l, alreadydefvars), op, 
                                checkAndUpdateEquationType(ops, currentLine)(r, alreadydefvars))
             
                    new CaseEq(css map(ce => (checkAndUpdateEquationType(ops, currentLine)(ce._1, alreadydefvars), checkAndTypeLogicTerm(ce._2))))
        //top level logic:
        prog.adts foreach (checkNames)
        //gather all operations for type checking of equations
        val avOps = HashMap.from(prog.adts.foldLeft(List.empty[Operation])((o, adt) => 
                        o ++ adt.ops).toArray groupBy(op => op.name))
        val fst = prog.adts map checkAndUpdateTypes
        new Program(fst, prog.expr map (expr => checkAndUpdateEquationType(avOps, LineTracker.getLine(s"eq(${expr})"))(expr)))