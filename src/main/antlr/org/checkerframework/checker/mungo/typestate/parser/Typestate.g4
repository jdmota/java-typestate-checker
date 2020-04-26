grammar Typestate;

@header {
package org.checkerframework.checker.mungo.typestate.parser;
import org.checkerframework.checker.mungo.typestate.*;
import static org.checkerframework.checker.mungo.typestate.Position.tokenToPos;
import static org.checkerframework.checker.mungo.typestate.Utils.map;
}

// Info: https://github.com/antlr/antlr4/blob/master/doc/parser-rules.md

start returns [TDeclarationNode ast] :
  package_statement? import_statement* t=typestate_declaration
  {$ast=$t.ast;}
;

package_statement : 'package' ID ( '.' ID )* ';' ;

import_statement : 'import' ID ( '.' ID )* ( '.' '*' )? ';' ;

typestate_declaration returns [TDeclarationNode ast] :
  t='typestate' ID '{' typestate_body '}' EOF
  {$ast=new TDeclarationNode(tokenToPos($t), $ID.getText(), $typestate_body.states);}
;

typestate_body returns [List<TStateNode> states] :
  ( s+=state_declaration )*
  {$states=map($s, s -> s.node);}
;

state_declaration returns [TStateNode node] :
  name=ID '=' state
  {$node=new TStateNode(tokenToPos($name), $name.getText(), $state.node.getMethods());}
;

state returns [TStateNode node] :
  t='{' ( m+=method ( ',' m+=method )* )? '}'
  {$node=new TStateNode(tokenToPos($t), null, map($m, it -> it.node));}
;

method returns [TMethodNode node] locals [TNode destination] :
  return_type=ID name=ID '(' ( args+=ID ( ',' args+=ID )* )? ')' ':' (
    id {$destination=$id.node;} |
    state {$destination=$state.node;} |
    decision_state {$destination=$decision_state.node;}
  )
  {$node=new TMethodNode(tokenToPos($return_type), $return_type.getText(), $name.getText(), map($args, a -> a.getText()), $destination);}
;

decision_state returns [TDecisionStateNode node] :
  t='<' decisions+=decision ( ',' decisions+=decision )* '>'
  {$node=new TDecisionStateNode(tokenToPos($t), map($decisions, d -> d.node));}
;

decision returns [TDecisionNode node] :
  label=ID ':' (
    id {$node=new TDecisionNode(tokenToPos($label), $label.getText(), $id.node);} |
    state {$node=new TDecisionNode(tokenToPos($label), $label.getText(), $state.node);}
  )
;

id returns [TIdNode node] :
  ID
  {$node=new TIdNode(tokenToPos($ID), $ID.getText());}
;

// match identifiers
ID : [$_a-zA-Z]+[$_a-zA-Z0-9]* ;

// skip spaces, tabs, newlines
WS : [ \t\r\n]+ -> skip ;

// skip comments
BlockComment : '/*' .*? '*/' -> skip ;
LineComment : '//' ~[\r\n]* -> skip ;
