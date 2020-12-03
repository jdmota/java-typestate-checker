grammar Typestate;

@header {
package org.checkerframework.checker.jtc.typestate.parser;
import org.checkerframework.checker.jtc.typestate.*;
import static org.checkerframework.checker.jtc.typestate.Position.tokenToPos;
import static org.checkerframework.checker.jtc.typestate.Utils.map;
}

// Info: https://github.com/antlr/antlr4/blob/master/doc/parser-rules.md

start returns [TTypestateNode ast] locals [TPackageNode pkg] :
  ( p=package_statement {$pkg=$p.node;} )? ( i+=import_statement )* t=typestate_declaration
  {$ast=new TTypestateNode($pkg, map($i, i -> i.node), $t.node);}
;

ref returns [TRefNode node] :
  id {$node=$id.node;} |
  r=ref '.' id {$node=new TMemberNode($r.node.getPos(), $r.node, $id.node);}
;

package_statement returns [TPackageNode node] :
  t='package' ref ';'
  {$node=new TPackageNode(tokenToPos($t), $ref.node);}
;

import_statement returns [TImportNode node] :
  t='import' s='static'? ref ( '.' star='*' )? ';'
  {$node=new TImportNode(tokenToPos($t), $ref.node, $s != null, $star != null);}
;

typestate_declaration returns [TDeclarationNode node] :
  t='typestate' ID '{' typestate_body '}' EOF
  {$node=new TDeclarationNode(tokenToPos($t), $ID.getText(), $typestate_body.states);}
;

typestate_body returns [List<TStateNode> states] :
  ( s+=state_declaration )*
  {$states=map($s, s -> s.node);}
;

state_declaration returns [TStateNode node] :
  name=ID '=' state
  {$node=new TStateNode(tokenToPos($name), $name.getText(), $state.node.getMethods(), $state.node.isDroppable());}
;

state returns [TStateNode node] locals [boolean isDroppable] :
  t='{' ( m+=method ( ',' m+=method )* ( ',' DROP ':' END {$isDroppable=true;} )? )? '}'
  {$node=new TStateNode(tokenToPos($t), null, map($m, it -> it.node), $isDroppable);}
;

method returns [TMethodNode node] locals [TNode destination] :
  return_type=ref name=ID '(' ( args+=ref ( ',' args+=ref )* )? ')' ':' (
    ref {$destination=$ref.node;} |
    state {$destination=$state.node;} |
    decision_state {$destination=$decision_state.node;}
  )
  {$node=new TMethodNode($return_type.node.getPos(), $return_type.node, $name.getText(), map($args, a -> a.node), $destination);}
;

decision_state returns [TDecisionStateNode node] :
  t='<' decisions+=decision ( ',' decisions+=decision )* '>'
  {$node=new TDecisionStateNode(tokenToPos($t), map($decisions, d -> d.node));}
;

decision returns [TDecisionNode node] :
  label=ID ':' (
    ref {$node=new TDecisionNode(tokenToPos($label), $label.getText(), $ref.node);} |
    state {$node=new TDecisionNode(tokenToPos($label), $label.getText(), $state.node);}
  )
;

id returns [TIdNode node] :
  DROP {$node=new TIdNode(tokenToPos($DROP), $DROP.getText());} |
  END {$node=new TIdNode(tokenToPos($END), $END.getText());} |
  ID {$node=new TIdNode(tokenToPos($ID), $ID.getText());}
;

// keywords
DROP : 'drop' ;
END : 'end' ;

// match identifiers
ID : [$_a-zA-Z]+[$_a-zA-Z0-9]* ;

// skip spaces, tabs, newlines
WS : [ \t\r\n]+ -> skip ;

// skip comments
BlockComment : '/*' .*? '*/' -> skip ;
LineComment : '//' ~[\r\n]* -> skip ;
