grammar Typestate;

@header {
package org.checkerframework.checker.mungo.typestate;
import org.checkerframework.checker.mungo.typestate.ast.*;
import static org.checkerframework.checker.mungo.typestate.Utils.map;
}

// Info: https://github.com/antlr/antlr4/blob/master/doc/parser-rules.md

typestate_declaration returns [TDeclarationNode ast] :
  'typestate' ID '{' typestate_body '}' EOF
  {$ast=new TDeclarationNode($ID.getText(), $typestate_body.states);}
;

typestate_body returns [List<TStateNode> states] :
  ( s+=state_declaration ( ',' s+=state_declaration )* )?
  {$states=map($s, s -> s.node);}
;

state_declaration returns [TStateNode node] :
  ID '=' state
  {$node=new TStateNode($ID.getText(), $state.methods);}
;

state returns [List<TMethodNode> methods] :
  '{' ( m+=method ( ',' m+=method )* )? '}'
  {$methods=map($m, it -> it.node);}
;

method returns [TMethodNode node] locals [Object destination] :
  return_type=ID name=ID '(' ( args+=ID ( ',' args+=ID )* )? ')' ':' (
    dest=ID {$destination=$dest.getText();} |
    state {$destination=new TStateNode(null, $state.methods);} |
    decision_state {$destination=$decision_state.node;}
  )
  {$node=new TMethodNode($return_type.getText(), $name.getText(), map($args, a -> a.getText()), $destination);}
;

decision_state returns [TDecisionStateNode node] :
  '<' decisions+=decision ( ',' decisions+=decision )* '>'
  {$node=new TDecisionStateNode(map($decisions, d -> d.node));}
;

decision returns [TDecisionNode node] :
  label=ID ':' (
    dest=ID {$node=new TDecisionNode($label.getText(), $dest.getText());} |
    state {$node=new TDecisionNode($label.getText(), new TStateNode(null, $state.methods));}
  )
;

// match identifiers
ID : [$_a-zA-Z]+[$_a-zA-Z0-9]* ;

// skip spaces, tabs, newlines
WS : [ \t\r\n]+ -> skip ;
