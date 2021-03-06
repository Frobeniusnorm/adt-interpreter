
# adt-interpreter
```
            _  _            _         _                                   _               
           | || |          (_)       | |                                 | |              
  __ _   __| || |_  ______  _  _ __  | |_   ___  _ __  _ __   _ __   ___ | |_   ___  _ __ 
 / _` | / _` || __||______|| || '_ \ | __| / _ \| '__|| '_ \ | '__| / _ \| __| / _ \| '__|
| (_| || (_| || |_         | || | | || |_ |  __/| |   | |_) || |   |  __/| |_ |  __/| |   
 \__,_| \__,_| \__|        |_||_| |_| \__| \___||_|   | .__/ |_|    \___| \__| \___||_|   
                                                      | |                                 
                                                      |_|                                 
```
[![Scala CI](https://github.com/Frobeniusnorm/adt-interpreter/actions/workflows/scala.yml/badge.svg?branch=main)](https://github.com/Frobeniusnorm/adt-interpreter/actions/workflows/scala.yml)
## Features
Abstract Datatype (ADT) Parser, Type Checker and Interpreter. For language specification see below.
Interprets a notation type for ADTs and is able to evaluate equations based on the given axioms.
Supports definition of multiple axioms per file and interpretation of 
equations on top-level-scope. Those are allowed to access all operations of all Axioms
defined in that file.

## Usage
Download the precompiled binary (or build by yourself) and pass the to-evaluate adt file name on the command line as an argument.
You can pass several flags to customize or debug the output/execution:
  - "-d" or "--debug" start the interpreter in debug mode
  - "--nocolor" deactivates color codes
  - "-v" or "--verbose" additionally shows the original expression that was evaluated

## Build
You need the JDK 8 or higher, the Scala Compiler Version 3 and sbt. Then just clone the project and execute `sbt run` to build and run it.
If you want to generate executables use the command `assembly` in sbt i.e. `sbt assembly`.
The Executable will be written to: 
`target/scala-x.y.z/adt-interpreter-assembly-a.b.c.jar` (or just use the precompiled jar in the releases tab).

## Language Specification
Each ADT is created by a block that begins with `adt <name>` and ends with `end`.
Each ADT needs a `sorts <t1, t2, ...>`, an `ops` and an optional `axs` section.
So the basic structure of an adt looks like this:
``` 
adt <name>
sorts <t1, t2, ...>
ops
  <Operation Name>: <ParType> x <ParType> x ... -> <Return Type>
  <Operation Name>: <ParType> x <ParType> x ... -> <Return Type>
  ...
axs
  <Expression> = <Expression>
  <Expression> = <Expression>
  ...
end
```
Example for a Boolean Type:
```
adt Boolean
sorts Boolean
ops
    true:                      -> Boolean
    false:                     -> Boolean
    not:   Boolean             -> Boolean
    and:   Boolean x Boolean   -> Boolean
    or:    Boolean x Boolean   -> Boolean
axs
    not(true) = false
    not(false) = true
    and(true, x) = x
    and(false,x) = false
    or(true, x) = true
    or(false, x) = x
end
```
The ``sorts`` section imports operators from other types defined in the same file. The ADT Names in sorts are seperated by commas `,`.
Every Type in sorts which is not known or defined will be treated as a generic (type variable) and filled in during Interpretation.
The Operation Section lists all valid Operations and their types. Each Operation Definition consists of its name, followed by a `:` and the parameter types which are seperated by ` x `. After the parameter types the return types follows after an arrow `->`.
The ``axs``section provide reduction rules as equations. The left expression is then reducible to the right one (they allow an adt to be seen as a term rewriting system). 

Before, inbetween and after the axiom definitions, single expressions are allowed which will be evaluated to its normal form by the interpreter and printed on the console.
E.g. ``and(not(false), or(not(true), not(not(true))))`` will be evaluated to ``true``.
Operator overloading is only allowed between types, not in types itself. This means two adts are allowed to define operators with the same name as long they don't sort each other. During evaluation the operation with the correct type will be choosen, if both are possible the one earlier defined is used. Additionally case distinctions can be defined by this syntax on the right hand side of Axioms:
```
  <Expression> = | <Expression> if <Condition>
                 | <Expression> if <Condition>
                 |   ...
                 | <Expression> else
```
An Condition may include conjunctions with the `&` operator, disjunctions with the `|` operator and comparisons of Equations, which will be evaluated as far as possible and variables will be replaced by their equations from the left hand side, they match if the left hand side and the right hand side fulfill the comparison operator which can be either `=` for equality or `!=` for inequality. Its allowed to use brackets (terms in brackets will be evaluated first). The `&` operator binds stronger than the `|` operator, its only allowed to compare equations with equations.
The Condition may be else, which will always be fulfilled. The equation of the first matching condition will be chosen during the interpretation step.
Example for a partly redundant definition of an `xor` Axiom in the Boolean Type from above:
```
...
  xor(x, y) = | true if x = true & y = false | x = false & y = true | x != y
              | false else
...
```
It's possible to overload operations (define multiple operations with the same name), as long as they have different parameters and can be distinguished by them. This additionally requires variables in axioms to stand at positions where their type can be unambiguously be determined. Alternatively you can use namespaces
to differentiate operations with the same name with the syntax `<ADT Name>.<Operation Name>`.

You can include expressions between or after the adt definitions, that will be evaluated with the given given Axioms.
The result will be printed on stdout if the evaluation terminates.
Since the newest version the reduction strategy for the expressions is leftmost-innermost, before it followed haskells lambda calculus with leftmost-outermost, but innermost makes more sense for this definition.

It's possible to define constants for better readability which will be replaced before evaluation by their definition, the output will be transformed back.
They are defined in a single line by ``<Constant Name> := <Expression>`` e.g.
```
adt Nat
sorts Nat
ops
  zero:     -> Nat
  succ: Nat -> Nat
end

0:= zero
ONE:= succ(0)
2:= succ(ONE)
3:= succ(2)
succ(succ(ONE))
```
The last expression would be evaluated to ``3``.

## Contribute
Work through my unreadable code or just add feature wishes. I am more than happy to answer questions and review pull requests :)
