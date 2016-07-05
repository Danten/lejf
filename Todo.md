Edit programs

  * Since we are using a structural editor we should have commands/tactics
    to create programs.

Renamer

 * Check that all names make sense with regard to modules

Module/Lambda lift

 * Not sure I want all definitions be λ-lifted, or being explicit
   about closures

Typechecker

 * Complete it
 * Make it parallel

Specialiser

  * Templates should compile away at some point, figure out what
    algorithm to use

Backend

 * Going to LLVM Maybe? Or maybe start with a simple C backend
 * I also would like to have a javascipt backend

PrettyPrinter

 * Need to fix QName printing to use shortest name possible