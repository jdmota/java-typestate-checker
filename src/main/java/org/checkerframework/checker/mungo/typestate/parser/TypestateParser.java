// Generated from org\checkerframework\checker\mungo\typestate\parser\Typestate.g4 by ANTLR 4.8

package org.checkerframework.checker.mungo.typestate.parser;
import org.checkerframework.checker.mungo.typestate.ast.*;
import static org.checkerframework.checker.mungo.typestate.ast.Position.tokenToPos;
import static org.checkerframework.checker.mungo.typestate.Utils.map;

import org.antlr.v4.runtime.atn.*;
import org.antlr.v4.runtime.dfa.DFA;
import org.antlr.v4.runtime.*;
import org.antlr.v4.runtime.misc.*;
import org.antlr.v4.runtime.tree.*;
import java.util.List;
import java.util.Iterator;
import java.util.ArrayList;

@SuppressWarnings({"all", "warnings", "unchecked", "unused", "cast"})
public class TypestateParser extends Parser {
	static { RuntimeMetaData.checkVersion("4.8", RuntimeMetaData.VERSION); }

	protected static final DFA[] _decisionToDFA;
	protected static final PredictionContextCache _sharedContextCache =
		new PredictionContextCache();
	public static final int
		T__0=1, T__1=2, T__2=3, T__3=4, T__4=5, T__5=6, T__6=7, T__7=8, T__8=9, 
		T__9=10, ID=11, WS=12;
	public static final int
		RULE_typestate_declaration = 0, RULE_typestate_body = 1, RULE_state_declaration = 2, 
		RULE_state = 3, RULE_method = 4, RULE_decision_state = 5, RULE_decision = 6, 
		RULE_id = 7;
	private static String[] makeRuleNames() {
		return new String[] {
			"typestate_declaration", "typestate_body", "state_declaration", "state", 
			"method", "decision_state", "decision", "id"
		};
	}
	public static final String[] ruleNames = makeRuleNames();

	private static String[] makeLiteralNames() {
		return new String[] {
			null, "'typestate'", "'{'", "'}'", "'='", "','", "'('", "')'", "':'", 
			"'<'", "'>'"
		};
	}
	private static final String[] _LITERAL_NAMES = makeLiteralNames();
	private static String[] makeSymbolicNames() {
		return new String[] {
			null, null, null, null, null, null, null, null, null, null, null, "ID", 
			"WS"
		};
	}
	private static final String[] _SYMBOLIC_NAMES = makeSymbolicNames();
	public static final Vocabulary VOCABULARY = new VocabularyImpl(_LITERAL_NAMES, _SYMBOLIC_NAMES);

	/**
	 * @deprecated Use {@link #VOCABULARY} instead.
	 */
	@Deprecated
	public static final String[] tokenNames;
	static {
		tokenNames = new String[_SYMBOLIC_NAMES.length];
		for (int i = 0; i < tokenNames.length; i++) {
			tokenNames[i] = VOCABULARY.getLiteralName(i);
			if (tokenNames[i] == null) {
				tokenNames[i] = VOCABULARY.getSymbolicName(i);
			}

			if (tokenNames[i] == null) {
				tokenNames[i] = "<INVALID>";
			}
		}
	}

	@Override
	@Deprecated
	public String[] getTokenNames() {
		return tokenNames;
	}

	@Override

	public Vocabulary getVocabulary() {
		return VOCABULARY;
	}

	@Override
	public String getGrammarFileName() { return "Typestate.g4"; }

	@Override
	public String[] getRuleNames() { return ruleNames; }

	@Override
	public String getSerializedATN() { return _serializedATN; }

	@Override
	public ATN getATN() { return _ATN; }

	public TypestateParser(TokenStream input) {
		super(input);
		_interp = new ParserATNSimulator(this,_ATN,_decisionToDFA,_sharedContextCache);
	}

	public static class Typestate_declarationContext extends ParserRuleContext {
		public TDeclarationNode ast;
		public Token t;
		public Token ID;
		public Typestate_bodyContext typestate_body;
		public TerminalNode ID() { return getToken(TypestateParser.ID, 0); }
		public Typestate_bodyContext typestate_body() {
			return getRuleContext(Typestate_bodyContext.class,0);
		}
		public TerminalNode EOF() { return getToken(TypestateParser.EOF, 0); }
		public Typestate_declarationContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_typestate_declaration; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof TypestateListener ) ((TypestateListener)listener).enterTypestate_declaration(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof TypestateListener ) ((TypestateListener)listener).exitTypestate_declaration(this);
		}
	}

	public final Typestate_declarationContext typestate_declaration() throws RecognitionException {
		Typestate_declarationContext _localctx = new Typestate_declarationContext(_ctx, getState());
		enterRule(_localctx, 0, RULE_typestate_declaration);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(16);
			((Typestate_declarationContext)_localctx).t = match(T__0);
			setState(17);
			((Typestate_declarationContext)_localctx).ID = match(ID);
			setState(18);
			match(T__1);
			setState(19);
			((Typestate_declarationContext)_localctx).typestate_body = typestate_body();
			setState(20);
			match(T__2);
			setState(21);
			match(EOF);
			((Typestate_declarationContext)_localctx).ast = new TDeclarationNode(tokenToPos(((Typestate_declarationContext)_localctx).t), ((Typestate_declarationContext)_localctx).ID.getText(), ((Typestate_declarationContext)_localctx).typestate_body.states);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class Typestate_bodyContext extends ParserRuleContext {
		public List<TStateNode> states;
		public State_declarationContext state_declaration;
		public List<State_declarationContext> s = new ArrayList<State_declarationContext>();
		public List<State_declarationContext> state_declaration() {
			return getRuleContexts(State_declarationContext.class);
		}
		public State_declarationContext state_declaration(int i) {
			return getRuleContext(State_declarationContext.class,i);
		}
		public Typestate_bodyContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_typestate_body; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof TypestateListener ) ((TypestateListener)listener).enterTypestate_body(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof TypestateListener ) ((TypestateListener)listener).exitTypestate_body(this);
		}
	}

	public final Typestate_bodyContext typestate_body() throws RecognitionException {
		Typestate_bodyContext _localctx = new Typestate_bodyContext(_ctx, getState());
		enterRule(_localctx, 2, RULE_typestate_body);
		int _la;
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(27);
			_errHandler.sync(this);
			_la = _input.LA(1);
			while (_la==ID) {
				{
				{
				setState(24);
				((Typestate_bodyContext)_localctx).state_declaration = state_declaration();
				((Typestate_bodyContext)_localctx).s.add(((Typestate_bodyContext)_localctx).state_declaration);
				}
				}
				setState(29);
				_errHandler.sync(this);
				_la = _input.LA(1);
			}
			((Typestate_bodyContext)_localctx).states = map(((Typestate_bodyContext)_localctx).s, s -> s.node);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class State_declarationContext extends ParserRuleContext {
		public TStateNode node;
		public Token name;
		public StateContext state;
		public StateContext state() {
			return getRuleContext(StateContext.class,0);
		}
		public TerminalNode ID() { return getToken(TypestateParser.ID, 0); }
		public State_declarationContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_state_declaration; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof TypestateListener ) ((TypestateListener)listener).enterState_declaration(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof TypestateListener ) ((TypestateListener)listener).exitState_declaration(this);
		}
	}

	public final State_declarationContext state_declaration() throws RecognitionException {
		State_declarationContext _localctx = new State_declarationContext(_ctx, getState());
		enterRule(_localctx, 4, RULE_state_declaration);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(32);
			((State_declarationContext)_localctx).name = match(ID);
			setState(33);
			match(T__3);
			setState(34);
			((State_declarationContext)_localctx).state = state();
			((State_declarationContext)_localctx).node = new TStateNode(tokenToPos(((State_declarationContext)_localctx).name), ((State_declarationContext)_localctx).name.getText(), ((State_declarationContext)_localctx).state.node.getMethods());
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class StateContext extends ParserRuleContext {
		public TStateNode node;
		public Token t;
		public MethodContext method;
		public List<MethodContext> m = new ArrayList<MethodContext>();
		public List<MethodContext> method() {
			return getRuleContexts(MethodContext.class);
		}
		public MethodContext method(int i) {
			return getRuleContext(MethodContext.class,i);
		}
		public StateContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_state; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof TypestateListener ) ((TypestateListener)listener).enterState(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof TypestateListener ) ((TypestateListener)listener).exitState(this);
		}
	}

	public final StateContext state() throws RecognitionException {
		StateContext _localctx = new StateContext(_ctx, getState());
		enterRule(_localctx, 6, RULE_state);
		int _la;
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(37);
			((StateContext)_localctx).t = match(T__1);
			setState(46);
			_errHandler.sync(this);
			_la = _input.LA(1);
			if (_la==ID) {
				{
				setState(38);
				((StateContext)_localctx).method = method();
				((StateContext)_localctx).m.add(((StateContext)_localctx).method);
				setState(43);
				_errHandler.sync(this);
				_la = _input.LA(1);
				while (_la==T__4) {
					{
					{
					setState(39);
					match(T__4);
					setState(40);
					((StateContext)_localctx).method = method();
					((StateContext)_localctx).m.add(((StateContext)_localctx).method);
					}
					}
					setState(45);
					_errHandler.sync(this);
					_la = _input.LA(1);
				}
				}
			}

			setState(48);
			match(T__2);
			((StateContext)_localctx).node = new TStateNode(tokenToPos(((StateContext)_localctx).t), null, map(((StateContext)_localctx).m, it -> it.node));
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class MethodContext extends ParserRuleContext {
		public TMethodNode node;
		public TNode destination;
		public Token return_type;
		public Token name;
		public Token ID;
		public List<Token> args = new ArrayList<Token>();
		public IdContext id;
		public StateContext state;
		public Decision_stateContext decision_state;
		public List<TerminalNode> ID() { return getTokens(TypestateParser.ID); }
		public TerminalNode ID(int i) {
			return getToken(TypestateParser.ID, i);
		}
		public IdContext id() {
			return getRuleContext(IdContext.class,0);
		}
		public StateContext state() {
			return getRuleContext(StateContext.class,0);
		}
		public Decision_stateContext decision_state() {
			return getRuleContext(Decision_stateContext.class,0);
		}
		public MethodContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_method; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof TypestateListener ) ((TypestateListener)listener).enterMethod(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof TypestateListener ) ((TypestateListener)listener).exitMethod(this);
		}
	}

	public final MethodContext method() throws RecognitionException {
		MethodContext _localctx = new MethodContext(_ctx, getState());
		enterRule(_localctx, 8, RULE_method);
		int _la;
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(51);
			((MethodContext)_localctx).return_type = match(ID);
			setState(52);
			((MethodContext)_localctx).name = match(ID);
			setState(53);
			match(T__5);
			setState(62);
			_errHandler.sync(this);
			_la = _input.LA(1);
			if (_la==ID) {
				{
				setState(54);
				((MethodContext)_localctx).ID = match(ID);
				((MethodContext)_localctx).args.add(((MethodContext)_localctx).ID);
				setState(59);
				_errHandler.sync(this);
				_la = _input.LA(1);
				while (_la==T__4) {
					{
					{
					setState(55);
					match(T__4);
					setState(56);
					((MethodContext)_localctx).ID = match(ID);
					((MethodContext)_localctx).args.add(((MethodContext)_localctx).ID);
					}
					}
					setState(61);
					_errHandler.sync(this);
					_la = _input.LA(1);
				}
				}
			}

			setState(64);
			match(T__6);
			setState(65);
			match(T__7);
			setState(75);
			_errHandler.sync(this);
			switch (_input.LA(1)) {
			case ID:
				{
				setState(66);
				((MethodContext)_localctx).id = id();
				((MethodContext)_localctx).destination = ((MethodContext)_localctx).id.node;
				}
				break;
			case T__1:
				{
				setState(69);
				((MethodContext)_localctx).state = state();
				((MethodContext)_localctx).destination = ((MethodContext)_localctx).state.node;
				}
				break;
			case T__8:
				{
				setState(72);
				((MethodContext)_localctx).decision_state = decision_state();
				((MethodContext)_localctx).destination = ((MethodContext)_localctx).decision_state.node;
				}
				break;
			default:
				throw new NoViableAltException(this);
			}
			((MethodContext)_localctx).node = new TMethodNode(tokenToPos(((MethodContext)_localctx).return_type), ((MethodContext)_localctx).return_type.getText(), ((MethodContext)_localctx).name.getText(), map(((MethodContext)_localctx).args, a -> a.getText()), _localctx.destination);
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class Decision_stateContext extends ParserRuleContext {
		public TDecisionStateNode node;
		public Token t;
		public DecisionContext decision;
		public List<DecisionContext> decisions = new ArrayList<DecisionContext>();
		public List<DecisionContext> decision() {
			return getRuleContexts(DecisionContext.class);
		}
		public DecisionContext decision(int i) {
			return getRuleContext(DecisionContext.class,i);
		}
		public Decision_stateContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_decision_state; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof TypestateListener ) ((TypestateListener)listener).enterDecision_state(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof TypestateListener ) ((TypestateListener)listener).exitDecision_state(this);
		}
	}

	public final Decision_stateContext decision_state() throws RecognitionException {
		Decision_stateContext _localctx = new Decision_stateContext(_ctx, getState());
		enterRule(_localctx, 10, RULE_decision_state);
		int _la;
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(79);
			((Decision_stateContext)_localctx).t = match(T__8);
			setState(80);
			((Decision_stateContext)_localctx).decision = decision();
			((Decision_stateContext)_localctx).decisions.add(((Decision_stateContext)_localctx).decision);
			setState(85);
			_errHandler.sync(this);
			_la = _input.LA(1);
			while (_la==T__4) {
				{
				{
				setState(81);
				match(T__4);
				setState(82);
				((Decision_stateContext)_localctx).decision = decision();
				((Decision_stateContext)_localctx).decisions.add(((Decision_stateContext)_localctx).decision);
				}
				}
				setState(87);
				_errHandler.sync(this);
				_la = _input.LA(1);
			}
			setState(88);
			match(T__9);
			((Decision_stateContext)_localctx).node = new TDecisionStateNode(tokenToPos(((Decision_stateContext)_localctx).t), map(((Decision_stateContext)_localctx).decisions, d -> d.node));
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class DecisionContext extends ParserRuleContext {
		public TDecisionNode node;
		public Token label;
		public IdContext id;
		public StateContext state;
		public TerminalNode ID() { return getToken(TypestateParser.ID, 0); }
		public IdContext id() {
			return getRuleContext(IdContext.class,0);
		}
		public StateContext state() {
			return getRuleContext(StateContext.class,0);
		}
		public DecisionContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_decision; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof TypestateListener ) ((TypestateListener)listener).enterDecision(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof TypestateListener ) ((TypestateListener)listener).exitDecision(this);
		}
	}

	public final DecisionContext decision() throws RecognitionException {
		DecisionContext _localctx = new DecisionContext(_ctx, getState());
		enterRule(_localctx, 12, RULE_decision);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(91);
			((DecisionContext)_localctx).label = match(ID);
			setState(92);
			match(T__7);
			setState(99);
			_errHandler.sync(this);
			switch (_input.LA(1)) {
			case ID:
				{
				setState(93);
				((DecisionContext)_localctx).id = id();
				((DecisionContext)_localctx).node = new TDecisionNode(tokenToPos(((DecisionContext)_localctx).label), ((DecisionContext)_localctx).label.getText(), ((DecisionContext)_localctx).id.node);
				}
				break;
			case T__1:
				{
				setState(96);
				((DecisionContext)_localctx).state = state();
				((DecisionContext)_localctx).node = new TDecisionNode(tokenToPos(((DecisionContext)_localctx).label), ((DecisionContext)_localctx).label.getText(), ((DecisionContext)_localctx).state.node);
				}
				break;
			default:
				throw new NoViableAltException(this);
			}
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static class IdContext extends ParserRuleContext {
		public TIdNode node;
		public Token ID;
		public TerminalNode ID() { return getToken(TypestateParser.ID, 0); }
		public IdContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_id; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof TypestateListener ) ((TypestateListener)listener).enterId(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof TypestateListener ) ((TypestateListener)listener).exitId(this);
		}
	}

	public final IdContext id() throws RecognitionException {
		IdContext _localctx = new IdContext(_ctx, getState());
		enterRule(_localctx, 14, RULE_id);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(101);
			((IdContext)_localctx).ID = match(ID);
			((IdContext)_localctx).node = new TIdNode(tokenToPos(((IdContext)_localctx).ID), ((IdContext)_localctx).ID.getText());
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			exitRule();
		}
		return _localctx;
	}

	public static final String _serializedATN =
		"\3\u608b\ua72a\u8133\ub9ed\u417c\u3be7\u7786\u5964\3\16k\4\2\t\2\4\3\t"+
		"\3\4\4\t\4\4\5\t\5\4\6\t\6\4\7\t\7\4\b\t\b\4\t\t\t\3\2\3\2\3\2\3\2\3\2"+
		"\3\2\3\2\3\2\3\3\7\3\34\n\3\f\3\16\3\37\13\3\3\3\3\3\3\4\3\4\3\4\3\4\3"+
		"\4\3\5\3\5\3\5\3\5\7\5,\n\5\f\5\16\5/\13\5\5\5\61\n\5\3\5\3\5\3\5\3\6"+
		"\3\6\3\6\3\6\3\6\3\6\7\6<\n\6\f\6\16\6?\13\6\5\6A\n\6\3\6\3\6\3\6\3\6"+
		"\3\6\3\6\3\6\3\6\3\6\3\6\3\6\5\6N\n\6\3\6\3\6\3\7\3\7\3\7\3\7\7\7V\n\7"+
		"\f\7\16\7Y\13\7\3\7\3\7\3\7\3\b\3\b\3\b\3\b\3\b\3\b\3\b\3\b\5\bf\n\b\3"+
		"\t\3\t\3\t\3\t\2\2\n\2\4\6\b\n\f\16\20\2\2\2k\2\22\3\2\2\2\4\35\3\2\2"+
		"\2\6\"\3\2\2\2\b\'\3\2\2\2\n\65\3\2\2\2\fQ\3\2\2\2\16]\3\2\2\2\20g\3\2"+
		"\2\2\22\23\7\3\2\2\23\24\7\r\2\2\24\25\7\4\2\2\25\26\5\4\3\2\26\27\7\5"+
		"\2\2\27\30\7\2\2\3\30\31\b\2\1\2\31\3\3\2\2\2\32\34\5\6\4\2\33\32\3\2"+
		"\2\2\34\37\3\2\2\2\35\33\3\2\2\2\35\36\3\2\2\2\36 \3\2\2\2\37\35\3\2\2"+
		"\2 !\b\3\1\2!\5\3\2\2\2\"#\7\r\2\2#$\7\6\2\2$%\5\b\5\2%&\b\4\1\2&\7\3"+
		"\2\2\2\'\60\7\4\2\2(-\5\n\6\2)*\7\7\2\2*,\5\n\6\2+)\3\2\2\2,/\3\2\2\2"+
		"-+\3\2\2\2-.\3\2\2\2.\61\3\2\2\2/-\3\2\2\2\60(\3\2\2\2\60\61\3\2\2\2\61"+
		"\62\3\2\2\2\62\63\7\5\2\2\63\64\b\5\1\2\64\t\3\2\2\2\65\66\7\r\2\2\66"+
		"\67\7\r\2\2\67@\7\b\2\28=\7\r\2\29:\7\7\2\2:<\7\r\2\2;9\3\2\2\2<?\3\2"+
		"\2\2=;\3\2\2\2=>\3\2\2\2>A\3\2\2\2?=\3\2\2\2@8\3\2\2\2@A\3\2\2\2AB\3\2"+
		"\2\2BC\7\t\2\2CM\7\n\2\2DE\5\20\t\2EF\b\6\1\2FN\3\2\2\2GH\5\b\5\2HI\b"+
		"\6\1\2IN\3\2\2\2JK\5\f\7\2KL\b\6\1\2LN\3\2\2\2MD\3\2\2\2MG\3\2\2\2MJ\3"+
		"\2\2\2NO\3\2\2\2OP\b\6\1\2P\13\3\2\2\2QR\7\13\2\2RW\5\16\b\2ST\7\7\2\2"+
		"TV\5\16\b\2US\3\2\2\2VY\3\2\2\2WU\3\2\2\2WX\3\2\2\2XZ\3\2\2\2YW\3\2\2"+
		"\2Z[\7\f\2\2[\\\b\7\1\2\\\r\3\2\2\2]^\7\r\2\2^e\7\n\2\2_`\5\20\t\2`a\b"+
		"\b\1\2af\3\2\2\2bc\5\b\5\2cd\b\b\1\2df\3\2\2\2e_\3\2\2\2eb\3\2\2\2f\17"+
		"\3\2\2\2gh\7\r\2\2hi\b\t\1\2i\21\3\2\2\2\n\35-\60=@MWe";
	public static final ATN _ATN =
		new ATNDeserializer().deserialize(_serializedATN.toCharArray());
	static {
		_decisionToDFA = new DFA[_ATN.getNumberOfDecisions()];
		for (int i = 0; i < _ATN.getNumberOfDecisions(); i++) {
			_decisionToDFA[i] = new DFA(_ATN.getDecisionState(i), i);
		}
	}
}