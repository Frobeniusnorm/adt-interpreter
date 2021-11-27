import scala.collection.immutable.HashMap
import scala.collection.immutable.HashSet

object Parser:
    def parseProgram(prog:Program):Program = 
        val namespaces:HashMap[String, HashSet[Operation]] = HashMap.from(prog.adts map(x => x.name -> x.ops))
        //helper functions:
        def checkNames(adt:ADT) = 
            val knownTypes = HashSet.from(namespaces filter(x => adt.sorts contains(x._1)) map(x => x._1))
            //check operation names        
            for op <- adt.ops do
                for t <- op.par :+ op.ret do
                    if !(knownTypes contains t) then 
                        throw new RuntimeException("Unknown Type \"" + t + "\" in ops of \"" + adt.name + "\"")
        
        def checkAndUpdateTypes(adt:ADT):ADT =
            val knownOps = HashMap.from(namespaces filter(x => adt.sorts contains(x._1)) flatMap(x => x._2) map(x => x.name -> x))
            def checker = checkAndUpdateEquationType(knownOps)
            val axs = adt.axs map (x => 
                val left = checker(x.left)
                val rightc = checker(x.right)
                left match
                    case AtomEq(name, None) => throw new RuntimeException("Illegal atomic operation \"" + name + "\" on left hand side!")
                    case AtomEq(name, Some(_)) => throw new RuntimeException("Illegal single variable \"" + name + "\" on left hand side!")
                    case _ => //that's fine
                val right = rightc match
                    case AtomEq(name, Some(_)) => left match
                        case RecEq(namer, _) => AtomEq(name, Some(knownOps(namer).ret)) 
                    case e => e
                          
                right.getVariables foreach((v1, ae1) =>
                    if !left.getVariables.contains(v1) then
                        throw new RuntimeException("Unknown Variable \"" + v1 + "\" on right hand side of Axiom!")
                    val ae2 = left.getVariables(v1)
                    if ae1.varType.isEmpty then
                        throw new RuntimeException("Variable on right hand sind has no type (wtf)!")
                    if ae2.varType.isEmpty then
                        throw new RuntimeException("Variable on left hand sind has no type (wtf)!")
                    if ae1.varType.get != ae2.varType.get then
                        throw new RuntimeException("Type error: could not match variable type for \"" + v1 + "\"! " +
                          "Type of variable on left hand side: \"" + ae2.varType.get + "\", on right hand side: \"" + ae1.varType.get + "\"")
                )
                new Axiom(left, right)
            )
            new ADT(adt.name, axs, adt.ops, adt.sorts)
        //Every Equation must be typable, since it only has one outer operation
        /** Updates AtomicEq which are variables and checks if the type of the equation is complete */ 
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
                                case AtomEq(name, Some(_)) => 
                                    AtomEq(name, Some(zeqp._1))
                                case _ =>
                                    if !(ops contains sep.operation) || !(ops(sep.operation).ret equals zeqp._1) then
                                        throw new RuntimeException("Type error: could not match \"" + sep.operation + "\" with expected type \"" + zeqp._1 + "\" in function call for \"" + name + "\"")
                                    sep
                    new RecEq(name, np)
        //top level logic:
        prog.adts foreach (checkNames)
        new Program(prog.adts map checkAndUpdateTypes, prog.expr)
                            
            

            