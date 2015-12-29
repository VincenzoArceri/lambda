
require "modules/substitution.k"

module LAMBDA-SYNTAX

  syntax Val ::= Id
               | "lambda" Id "." Exp  [binder]
  syntax Exp ::= Val
               | Exp Exp              [left, strict]
               | "(" Exp ")"          [bracket]

  syntax Val ::= Int | Bool

  syntax Exp ::= Exp "*" Exp          [strict, left]
               | Exp "/" Exp          [strict]
               > Exp "+" Exp          [strict, left]
               > Exp "<=" Exp         [strict]
               | Exp ">=" Exp         [strict]

  syntax Exp ::= "if" Exp "then" Exp "else" Exp  [strict(1)]         
               | "let" Id "=" Exp "in" Exp                          
               | "letrec" Id Id "=" Exp "in" Exp                     
               | "fix" Id "." Exp      [binder]  
  syntax KVariable ::= Id
endmodule

module LAMBDA
  imports LAMBDA-SYNTAX
  imports SUBSTITUTION

  syntax KResult ::= Val

  rule (lambda X:Id . E:Exp) V:Val => E[V / X]

  rule I1:Int * I2:Int => I1 *Int I2
  rule I1:Int / I2:Int => I1 /Int I2  when I2 =/=Int 0
  rule I1:Int + I2:Int => I1 +Int I2
  rule I1:Int <= I2:Int => I1 <=Int I2
  rule I1:Int >= I2:Int => I1 >=Int I2


  rule if true  then E else _ => E
  rule if false then _ else E => E

  rule let X = E in E':Exp => (lambda X . E') E                         [macro]

  rule letrec F:Id X:Id = E in E' => let F = fix F . lambda X . E in E' [macro]
  rule fix X . E => E[(fix X . E) / X]
endmodule