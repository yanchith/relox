# relox

My rust port of the Lox (jlox) interpreter from the [Crafting
Interpreters](http://craftinginterpreters.com/) book.

At the moment this is more or less an implementation of the vanilla
Lox language, with only some of the challenges incorporated. I have a
fair amount of cleanup to do (there are "a few" FIXMEs laying around
in the code for my future, less lazy self), most notably strings and
idents could use interning, and the error reporting could always
provide token span information (as it does in jlox).

### Notable changes from jlox

These are mostly driven by the differences between java and rust.

- There is no garbage collector to piggyback on, so refcounted
  pointers are used.
- ADTs and pattern matching instead of the visitor pattern.
- Not everything is a class, because it doesn't need to be.

Otherwise, this should be very recognizable as the original jlox.
