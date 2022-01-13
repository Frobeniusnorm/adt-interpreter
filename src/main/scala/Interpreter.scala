import scala.collection.immutable.HashSet
import scala.collection.immutable.HashMap
import scala.collection.mutable.OpenHashMap
import java.io.InputStreamReader
import java.io.BufferedReader

class Interpreter(prog:Program, debug:Boolean = false):
    val (avOps, avAxs) = typeAndCollectAxioms(prog)
    val evaledExpr = (prog.expr map (x => reduceEquation(x, LineTracker.getLine(s"eq(${x.toString})"))))
    /**
     * Collects and Hashes all operations and Axioms
     */ 
    def typeAndCollectAxioms(prog:Program) =
        val avOps = HashMap.from(prog.adts.foldLeft(List.empty[Operation])((o, adt) => 
                        o ++ adt.ops).toArray groupBy(op => op.name))
        //Hash Axioms by their first operation on left hand Side for faster pattern matching
        val avAxs = HashMap.from(prog.adts flatMap(adt => 
            adt.axs) groupBy (axs => axs.left.operation))
        (avOps, avAxs)
    /**
     * Applies applyMatching as long as it matches something
     */ 
    def reduceEquation(e:Equation, line:Int):Equation =
        var reader:Option[BufferedReader] = None 
        if debug then
            println("Reducing Equation: " + e)
            reader = Some(new BufferedReader(new InputStreamReader(System.in)))
        var x = e
        var m = applyMatching(x, line)
        var seen = HashSet.empty[String]
        while !m.isEmpty do 
            x = m.get
            if debug then
                println(" = " + x)
                reader.get.readLine()
            if seen contains x.toString then
                throw InfiniteRecursionException("Infinite Recursion: Axioms will be applied infinite times on this term!", line)
            seen = seen + x.toString
            m = applyMatching(x, line)
        x
    /**
     * Trys to find an matching axiom, if found applies it, else
     * tries to match one of the parameter equations if the equation itself is a recursive equation.
     * @return None if no axiom could be matched on the Equation, else Some(e) with e being the transformed equation
     */
    def applyMatching(e:Equation, line:Int):Option[Equation] = 
        e match
            case x:AtomEq => None
            case x:RecEq =>
                var found = List.empty[(Int, Equation)]
                var i = 0
                while i < x.params.length do //sorry Curry and Howard and Holy Monad in heaven, forgive me my imperative sins
                    val rek = applyMatching(x.params(i), line)
                    if !rek.isEmpty then
                        found = (i, rek.get) :: found 
                    i += 1
                if found.isEmpty then //recursive no axiom matched => match this one
                    val matching = if !avAxs.contains(x.op) then Array.empty[(Axiom, HashMap[String, Equation])] //no axioms
                                    //find matching axioms, try to fill in vars, filter those which work, map to axiom and vars
                                    else avAxs(x.op) filter(ax => matches(ax.left, x)) map(ax => (ax, fillVariables(e, ax.left))) filter(
                                            ax => !ax._2.isEmpty) map(ax => (ax._1, ax._2.get))
                    if !matching.isEmpty then
                        Some(applyAxiom(x, matching.head._1, matching.head._2, line))
                    else None
                else 
                    val np = Array.from(x.params)
                    found.foreach((i, pe) => np(i) = pe)
                    val rer = new RecEq(x.op, np)
                    rer.ref_op = x.ref_op
                    Some(rer)
                
                    
    /**
     * Checks if @param e matches @param ax, ax is usually the left hand side of an axiom
     */ 
    def matches(ax:Equation, e:Equation):Boolean = 
        ax match 
            case AtomEq(_, Some(t), _) => t.isGeneric || (e match
                case AtomEq(_, Some(et), _) => t == et
                case AtomEq(op, None, ns) => 
                    (if ns.isEmpty then avOps(op) else avOps(op) filter (_.orig_adt == ns.get)) exists (_.ret == t)
                case re:RecEq => 
                    re.ref_op.get.ret == t)
            case AtomEq(op, None, _) => e match
                case AtomEq(v, Some(t), _) => true
                case AtomEq(ep, None, _) => op == ep
                case _ => false
            case RecEq(op, opar, _) => e match
                case RecEq(ep, epar, _) =>
                    op == ep && opar.length == epar.length && ((opar zip epar) forall ((a, b) => matches(a, b)))
                case _ => false //no case matching needed here
        
    /**
     * Maps the Variables in @param ax to the expressions in @param e
     */ 
    def fillVariables(e:Equation, ax:Equation) : Option[HashMap[String, Equation]] = ax match
        case AtomEq(name, Some(_), _) => 
            Some(HashMap(name -> e))
        case AtomEq(op, None, _) => Some(HashMap.empty[String, Equation])
        case RecEq(op, pars, _) => e match
            case RecEq(ep, epar, _) => (epar zip pars).foldLeft(Some(
                HashMap.empty[String, Equation]).asInstanceOf[Option[HashMap[String, Equation]]]) ((acc, x) => acc match
                    case None => None //
                    case Some(otvar) =>
                        val rekvarop = fillVariables(x._1, x._2)
                        if !rekvarop.isEmpty && rekvarop.get.filter(x=> otvar.contains(x._1)).forall(x => otvar(x._1) == x._2) then
                            Some(otvar ++ rekvarop.get)
                        else None)

    def applyAxiom(e:Equation, ax:Axiom, vars:HashMap[String, Equation], line:Int) : Equation = 
        def visitEquationsAndReplace(a:Equation) : Equation = a match
            case AtomEq(name, Some(_), _) => vars(name)
            case AtomEq(name, None, _) => a
            case re:RecEq => 
                val foo = RecEq(re.op, re.params map visitEquationsAndReplace)
                foo.ref_op = re.ref_op
                foo
            case CaseEq(parts) =>
                val res = parts find(x => isLogicTerm(vars, line)(x._2))
                if res.isEmpty then throw new ExecutionException("Could not find fulfilling case predicate!", line)
                //res could be a single variable
                visitEquationsAndReplace(res.get._1)
            //Here evaluate CondEq with its logic terms etc.
        visitEquationsAndReplace(ax.right)

    def isLogicTerm(vars:(HashMap[String, Equation]), line:Int)(lt:LogicTerm):Boolean = 
        def rek = isLogicTerm(vars, line)
        def insertVars(e:Equation):Equation = e match
            case AtomEq(name, Some(_),_ ) => vars(name)
            case AtomEq(name, None, _) => e
            case re:RecEq => 
                val foo = RecEq(re.op, re.params map insertVars)
                foo.ref_op = re.ref_op
                foo
            case _ => throw new ExecutionException("Illegal equation type in logic term: " + e, line)
        lt match
            case Literal(Condition(x, e, y)) => 
                if x == null || y == null then true //else case
                else 
                    val eq1 = reduceEquation(insertVars(x), line)
                    val eq2 = reduceEquation(insertVars(y), line)
                    if e then eq1.toString == eq2.toString else eq1.toString != eq2.toString
            case Disjunction(parts) =>
                parts exists (rek)
            case Conjunction(parts) =>
                parts forall (rek)
