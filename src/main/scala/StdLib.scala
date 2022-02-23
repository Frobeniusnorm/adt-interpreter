import scala.collection.immutable.HashMap
object StdLib {
//TODO it would be a lot more efficient if i preprocess the parsing and define the Names and Nodes here
    var used = false
    def fromList(e:Equation, line:Int) = 
        def convert(eq:Equation):String = eq match
            case AtomEq("Nil", _, _) => "\""
            case RecEq("Cons", pars, _) =>
                if pars.length != 2 then
                    e.toString
                else
                    val el = pars(0).operation
                    if !el.startsWith("'") || !el.endsWith("'") then
                        e.toString
                    else el.substring(1, el.length - 1) + convert(pars(1))
            case _ => e.toString
        e match
            case RecEq("fromList", params, None) =>
                if params.length == 1 then
                    "\"" + convert(params(0))
                else e.toString
            case _ => e.toString
    def fromNat(e:Equation, line:Int) = 
        def helper(e:Equation):Option[Int] = e match
            case AtomEq("0", _, _) => Some(0)
            case AtomEq("zero", _, _) => Some(0)
            case AtomEq(numb, _, _) =>
                try
                    Some(numb.toInt)
                catch
                    case e:Exception => None
            case RecEq("succ", pars, _) =>
                if pars.length != 1 then
                    None
                else
                    val rek = helper(pars(0))
                    if !rek.isEmpty then Some(rek.get + 1)
                    else None
            case _ => None
        helper(e) match
            case Some(x) => "" + x
            case None => e.toString

    val outputFcts =
        HashMap(
            "fromList" -> fromList,
            "succ" -> fromNat,
            "zero" -> fromNat
        )
    val adts = Array(
"""adt Char
sorts Char,Nat
ops
    toNat: Char -> Nat
    fromNat: Nat -> Char""",    
"""adt String
sorts String, Nat, List
ops
    fromList: List -> String
    toList: String -> List
    concat: String x String -> String
    +:String x String -> String
    subString: String x Nat x Nat -> String
axs
    concat(fromList(a), fromList(b)) = fromList(concat(a, b)) //as List operation 
    String.+(a,b) = concat(a,b)
    subString(fromList(x), a, b) = fromList(subList(x, a, b))
    toList(fromList(x)) = x""",
"""adt IO
sorts Nat, String, IO
ops
    readNat: -> Nat
    readLine: -> String
    writeNat: -> IO
    writeString: -> IO""",
"""adt Nat
sorts Nat
ops
    zero:               -> Nat
    succ:   Nat         -> Nat
    pred:   Nat         -> Nat
    add:    Nat x Nat   -> Nat
    sub:    Nat x Nat   -> Nat
    mul:    Nat x Nat   -> Nat
    div:    Nat x Nat   -> Nat
    +:      Nat x Nat   -> Nat
    -:      Nat x Nat   -> Nat
    *:      Nat x Nat   -> Nat
    /:      Nat x Nat   -> Nat
axs
    pred(zero) = zero
    pred(succ(x)) = x
    add(zero, x) = x
    add(succ(x), y) = succ(add(x, y))
    sub(x, zero) = x
    sub(zero, x) = zero
    sub(succ(x), succ(y)) = sub(x,y)
    mul(x, zero) = zero
    mul(x, succ(y)) = add(x, mul(x,y))
    div(x, y) = | zero                              if sub(y,x) != zero
                | add(succ(zero), div(sub(x,y), y)) else
    +(x,y) = add(x,y)
    -(x,y) = sub(x,y)
    *(x,y) = mul(x,y)
    /(x,y) = div(x,y)""",
"""adt Boolean
sorts Boolean
ops
    true:                      -> Boolean

    false:                     -> Boolean
    not:   Boolean             -> Boolean
    and:   Boolean x Boolean   -> Boolean
    or:    Boolean x Boolean   -> Boolean
    xor:   Boolean x Boolean   -> Boolean
axs
    not(true) = false
    not(false) = true
    and(true, x) = x
    and(false,x) = false
    or(true, x) = true
    or(false, x) = x
    xor(x, y) = | true  if x != y
                | false else""",
"""adt List
sorts List, T, Boolean, Nat
ops
    Nil: -> List
    Cons: T x List -> List
    concat: List x List -> List
    head: List -> T
    tail: List -> List
    contains: List x T -> Boolean
    subList: List x Nat x Nat -> List
axs
    concat(Nil, x) = x
    concat(Cons(x, a), b) = Cons(x, concat(a,b))
    head(Cons(x, l)) = x
    tail(Cons(x, l)) = l

    contains(a, x) = | false                if a = Nil
                     | true                  if head(a) = x
                     | contains(tail(a), x)  else
    
    subList(Nil, x, y) = Nil
    subList(Cons(x, l), succ(x), succ(y)) = subList(l, x, y)
    subList(Cons(x, l), zero, succ(y)) = Cons(x, subList(l, zero, y))
    subList(Cons(x, l), zero, zero) = Nil""")
}
