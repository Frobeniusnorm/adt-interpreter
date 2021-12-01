# adt-interpreter
## Features
Abstract Datatype (ADT) Parser, Type Checker and Interpreter. For language specification see below.
Does NOT (yet) support operator overloading, though planned.
Does NOT (yet) support generic types.
Does support definition of multiple axioms per file and interpretation of 
equations on top-level-scope. Those are allowed to access all operations of all Axioms
defined in that file.

## Usage
Download the precompiled binary (or build by yourself) and pass the to-evaluate adt file name on the command line as an argument. There are no options yet.

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
The Operation Section lists all valid Operations and their types. Each Operation Definition consists of its name, followed by a `:` and the parameter types which are seperated by ` x `. After the parameter types the return types comes after an arrow `->`.
The ``axs``section provide reduction rules as equations. The left expression is then reducible to the right one (they allow an adt to be seen as a term rewriting system). 

Before, inbetween and after the axiom definitions, single expressions are allowed which will be evaluated to its normal form by the interpreter and printed on the console.
E.g. ``and(not(false), or(not(true), not(not(true))))`` will be evaluated to ``true``.
Operator overloading is only allowed between types, not in types itself. This means two adts are allowed to define operators with the same name as long they don't sort each other. During evaluation the operation with the correct type will be choosen, if both are possible the one earlier defined is used.

## TODOs
 - if - cases as braces
 - Type Overloading inside adts
 - Generic Types
 - More tests
 - Help command
 - interactive mode after reading adt definition with command line option

## Contribute
Work through my unreadable code and look at the todos. I am more than happy to answer questions and review pull requests :)
