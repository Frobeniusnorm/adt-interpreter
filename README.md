# adt-interpreter
## Features
Abstract Datatype (ADT) Parser, Type Checker and Interpreter. For language specification see below.
Does NOT (yet) support operator overloading, though planned.
Does NOT (yet) support generic types.
Does support definition of multiple axioms per file and interpretation of 
equations on top-level-scope. Those are allowed to access all operations of all Axioms
defined in that file.

## Build
You need the JDK 8 or higher, the Scala Compiler Version 3 and sbt. Then just clone the project and execute `sbt run` to build and run it.
If you want to generate executables use the command `assembly` in sbt i.e. `sbt assembly`.
The Executable will be written to: 
`target/scala-x.y.z/adt-interpreter-assembly-a.b.c.jar` (or just use the precompiled jar in the releases tab).

## Language Specification
