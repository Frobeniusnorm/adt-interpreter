import scala.collection.immutable.HashSet
import scala.collection.immutable.HashMap
import scala.collection.mutable.OpenHashMap

//idea: per iteration try from outer to inner to match axioms
//if in one iteration not a single axiom was matched => terminate 
//For each application of an axiom safe which variables have which names in the axiom

class Interpreter(prog:Program):
    val (avOps, avAxs) = typeAndCollectAxioms(prog)
    val evaledExpr = (prog.expr map reduceEquation)
    /**
     * Collects and Hashes all operations and Axioms
     */ 
    def typeAndCollectAxioms(prog:Program) =
        val avOps = HashMap.from(prog.adts.foldLeft(HashSet.empty[Operation])((o, adt) => 
                        o ++ adt.ops) map (op => op.name -> op))
        //Hash Axioms by their first operation on left hand Side for faster pattern matching
        val avAxs = HashMap.from(prog.adts flatMap(adt => 
            adt.axs groupBy (axs => axs.left.operation)))
        (avOps, avAxs)
    /**
     * Applies applyMatching as long as it matches something
     */ 
    def reduceEquation(e:Equation):Equation =
        var x = e
        var m = applyMatching(x)
        while !m.isEmpty do 
            x = m.get
            m = applyMatching(x)
        x
    /**
     * Trys to find an matching axiom, if found applys it, else
     * tries to match one of the parameter equations if the equation itself is a recursive equation.
     * @return None if no axiom could be matched on the Equation, else Some(e) with e being the transformed equation
     */
    def applyMatching(e:Equation):Option[Equation] = 
        e match
            case x:AtomEq => None
            case x:RecEq =>
                val matching = if !avAxs.contains(x.op) then None else avAxs(x.op) find(ax => matches(ax.left, x))
                if !matching.isEmpty then
                    Some(applyAxiom(x, matching.get))
                else
                    var found:Option[Equation] = None
                    var i = 0
                    while i < x.params.length && found.isEmpty do //sorry Curry and Howard and Holy Monad in heaven, forgive me my imperial sins
                        val rek = applyMatching(x.params(i))
                        if !rek.isEmpty then
                            found = rek
                        else i += 1
                    if found.isEmpty then
                        None
                    else 
                        val np = Array.from(x.params)
                        np(i) = found.get
                        Some(new RecEq(x.op, np))
    //TODO: fill and match type variables
    //to do that create HashTable for Type variables just as for normal variables one step further
    /**
     * Checks if @param e matches @param ax, ax is usually the left hand side of an axiom
     */ 
    def matches(ax:Equation, e:Equation):Boolean = 
        ax match 
            case AtomEq(_, Some(t)) => e match
                case AtomEq(_, Some(et)) => et == t
                case AtomEq(op, None) => avOps(op).ret == t
                case RecEq(op, _) => avOps(op).ret == t
            case AtomEq(op, None) => e match
                case AtomEq(v, Some(t)) => true
                case AtomEq(ep, None) => op == ep
                case _ => false
            case RecEq(op, opar) => e match
                case RecEq(ep, epar) =>
                    op == ep && ((opar zip epar) forall ((a, b) => matches(a, b)))
                case _ => false
    /**
     * Maps the Variables in @param ax to the expressions in @param e
     */ 
    def fillVariables(e:Equation, ax:Equation) : HashMap[String, Equation] = ax match
        case AtomEq(name, Some(_)) => HashMap(name -> e)
        case AtomEq(op, None) => HashMap.empty[String, Equation]
        case RecEq(op, pars) => e match
            case RecEq(ep, epar) => (epar zip pars).foldLeft(HashMap.empty[String, Equation]) ((acc, x) =>
                acc ++ fillVariables(x._1, x._2))

    def applyAxiom(e:Equation, ax:Axiom) : Equation = 
        val vars = fillVariables(e, ax.left)
        def visitEquationsAndReplace(a:Equation) : Equation = a match
            case AtomEq(name, Some(_)) => vars(name)
            case AtomEq(name, None) => a
            case RecEq(name, pars) => RecEq(name, pars map visitEquationsAndReplace)

        visitEquationsAndReplace(ax.right)
