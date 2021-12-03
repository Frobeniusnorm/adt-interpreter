import scala.collection.immutable.HashMap
import scala.collection.immutable.HashSet

object Parser:
    def parseProgram(prog:Program):Program = 
        val namespaces:HashMap[String, HashSet[Operation]] = HashMap.from(prog.adts map(x => x.name -> x.ops))
        //helper functions:
        /**
         * Checks if all used types appear in sorts
         */ 
        def checkNames(adt:ADT) = 
            //TODO all types that are not contained in namespaces -> local generics that may be used
            val knownTypes = HashSet.from(namespaces filter(x => adt.sorts contains(x._1)) map(x => x._1))
            //check operation names        
            for op <- adt.ops do
                for t <- op.par :+ op.ret do
                    if !(knownTypes contains t) then 
                        throw new RuntimeException("Unknown Type \"" + t + "\" in ops of \"" + adt.name + "\"")
        
        /**
         * Checks types of all axioms of an adt and sets the variable types
         */ 
        def checkAndUpdateTypes(adt:ADT):ADT =
            val knownOps = HashMap.from(namespaces filter(x => adt.sorts contains(x._1)) flatMap(x => x._2) map(x => x.name -> x))
            def checker = checkAndUpdateEquationType(knownOps)
            val axs = adt.axs map (x => 
                val left = checker(x.left)
                val rightc = checker(x.right)
                left match
                    case AtomEq(name, None) => throw new RuntimeException("Illegal atomic operation \"" + name + "\" on left hand side!")
                    case AtomEq(name, Some(_)) => throw new RuntimeException("Illegal single variable \"" + name + "\" on left hand side!")
                    case CaseEq(cases) => throw new RuntimeException("Illegal case statement on left hand side of Axiom!")
                    case _ => //that's fine
                val right = rightc match
                    case AtomEq(name, Some(_)) => left match
                        case RecEq(namer, _) => AtomEq(name, Some(knownOps(namer).ret)) 
                    case CaseEq(cases) => CaseEq(cases map (cs => (cs._1 match //in case of a case equation, type all single variables that occur as cases
                        case AtomEq(name, Some(_)) => left match
                            case RecEq(namer, _) => AtomEq(name, Some(knownOps(namer).ret))
                        case umc => umc
                    , cs._2)))
                    case e => e
                val leftvars = left.getVariables
                right.getVariables foreach((v1, ae1) =>
                    if !leftvars.contains(v1) then
                        throw new RuntimeException("Unknown Variable \"" + v1 + "\" on right hand side of Axiom!")
                    val ae2 = leftvars(v1)
                    if ae1.varType.isEmpty then
                        throw new RuntimeException("Variable on right hand sind has no type (wtf)!")
                    if ae2.varType.isEmpty then
                        throw new RuntimeException("Variable on left hand sind has no type (wtf)!")
                    if ae1.varType.get != ae2.varType.get then
                        throw new RuntimeException("Type error: could not match variable type for \"" + v1 + "\"! " +
                          "Type of variable on left hand side: \"" + ae2.varType.get + "\", on right hand side: \"" + ae1.varType.get + "\"")
                )
                //still have to check if term variables even exist and type them
                val fright = right match
                    case CaseEq(cases) => 
                        def completeVars(eq:Equation):Equation = eq match
                            case null => null
                            case AtomEq(name, _) => if leftvars.contains(name) then 
                                AtomEq(name, leftvars(name).varType)
                                else AtomEq(name, None)
                            case RecEq(name, parts) =>
                                if !(knownOps contains name) then throw new RuntimeException("Could not find operation \"" + name + "\"!") 
                                val op = knownOps(name)
                                RecEq(name, (parts zip op.par) map (p => 
                                    val rp = completeVars(p._1)
                                    val rpt = rp match 
                                        case AtomEq(namer, Some(t)) => t
                                        case AtomEq(namer, None) => knownOps(namer).ret
                                        case RecEq(namer, _) => knownOps(namer).ret
                                        case CaseEq(_) => throw new RuntimeException("Case Equations are not allowed to be recursively stacked!")
                                    if rpt != p._2 then throw new RuntimeException("Could not match type \"" + rpt + "\" with expected type \"" +p._2+ "\" in operation \"" + name + "\"")
                                    rp    
                                ))
                            case _ => throw new RuntimeException("Illegal Equation type in Condition: \"" + eq + "\"")
                        def completeTerms(lt:LogicTerm):LogicTerm = lt match
                            case Literal(Condition(x, e, y)) => Literal(Condition(completeVars(x), e, completeVars(y)))
                            case Conjunction(parts) => Conjunction(parts map completeTerms)
                            case Disjunction(parts) => Disjunction(parts map completeTerms)
                        CaseEq(cases map(ce => (ce._1, completeTerms(ce._2))))
                    case diff => diff
                new Axiom(left, fright)
            )
            new ADT(adt.name, axs, adt.ops, adt.sorts)
        //Every Equation must be typable, since it only has one outer operation
        /** Updates AtomicEq that are variables and checks if the type of the equation is complete */ 
        def checkAndUpdateEquationType(ops:HashMap[String, Operation])(eq:Equation) : Equation = 
            eq match
                case AtomEq(name, _) => if ops.contains(name) then AtomEq(name, None) else AtomEq(name, Some(""))
                case RecEq(name, e:Array[Equation]) =>
                    if !(ops contains name) then throw new RuntimeException("Unknown Operation \"" + name + "\"")
                    val op = ops(name)
                    if op.par.length != e.length then throw new RuntimeException("Not enough parameters for operation \"" + name + "\"")
                    val np = 
                        for zeqp <- (op.par zip e) yield
                            val sep = checkAndUpdateEquationType(ops)(zeqp._2)
                            sep match
                                case AtomEq(n2, Some(_)) => 
                                    AtomEq(n2, Some(zeqp._1))
                                case _ =>
                                    if !(ops contains sep.operation) || !(ops(sep.operation).ret equals zeqp._1) then
                                        throw new RuntimeException("Type error: could not match \"" + sep.operation + "\" with expected type \"" + zeqp._1 + "\" in function call for \"" + name + "\"")
                                    sep
                    new RecEq(name, np)
                case CaseEq(css) => 
                    new CaseEq(css map(ce => (checkAndUpdateEquationType(ops)(ce._1), ce._2)))
        //top level logic:
        prog.adts foreach (checkNames)
        new Program(prog.adts map checkAndUpdateTypes, prog.expr)
                            
            

            