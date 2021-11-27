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
            new ADT(adt.name, adt.axs map (x => new Axiom(checker(x.left), checker(x.right))), adt.ops, adt.sorts)
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
                            //TODO check if sep is atomiceq as var
                            sep match
                                case AtomEq(name, Some(_)) => AtomEq(name, Some(zeqp._1))
                                case _ =>
                                    if !(ops contains sep.operation) || !(ops(sep.operation).ret equals zeqp._1) then
                                        throw new RuntimeException("Type error: could not match \"" + sep.operation + "\" with expected type \"" + zeqp._1 + "\" in function call for \"" + name + "\"")
                                    sep
                    new RecEq(name, np)
        //top level logic:
        prog.adts foreach (checkNames)
        new Program(prog.adts map checkAndUpdateTypes)
                            
            

            