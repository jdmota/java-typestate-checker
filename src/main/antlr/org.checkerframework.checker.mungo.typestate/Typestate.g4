grammar Typestate;

@header {
package org.checkerframework.checker.mungo.typestate;
}

// Info: https://github.com/antlr/antlr4/blob/master/doc/parser-rules.md
// TODO use actions

typestate_declaration : 'typestate' name=ID '{' body=typestate_body '}' EOF ;

typestate_body : ( states+=state_declaration ( ',' states+=state_declaration )* )? ;

state_declaration : name=ID '=' inner=state ;

state : '{' body=state_body '}' ;

state_body : ( methods+=method ( ',' methods+=method )* )? ;

method : return_type=ID name=ID '(' ( args+=ID ( ',' args+=ID )* )? ')' ':' dest+=method_return ;

method_return : dest=destination | d=decision_state ;

decision_state : '<' decisions+=decision ( ',' decisions+=decision )* '>' ;

decision : name=ID ':' dest=destination ;

destination : end='end' | name=ID | inner=state ;

// match identifiers
ID : [$_a-zA-Z]+[$_a-zA-Z0-9]* ;

// skip spaces, tabs, newlines
WS : [ \t\r\n]+ -> skip ;
