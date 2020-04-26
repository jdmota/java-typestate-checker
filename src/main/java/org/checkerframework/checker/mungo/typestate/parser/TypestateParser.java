// Generated from org\checkerframework\checker\mungo\typestate\parser\Typestate.g4 by ANTLR 4.8

package org.checkerframework.checker.mungo.typestate.parser;
import org.checkerframework.checker.mungo.typestate.*;
import static org.checkerframework.checker.mungo.typestate.Position.tokenToPos;
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
		T__9=10, T__10=11, T__11=12, T__12=13, T__13=14, T__14=15, ID=16, WS=17, 
		BlockComment=18, LineComment=19;
	public static final int
		RULE_start = 0, RULE_package_statement = 1, RULE_import_statement = 2, 
		RULE_typestate_declaration = 3, RULE_typestate_body = 4, RULE_state_declaration = 5, 
		RULE_state = 6, RULE_method = 7, RULE_decision_state = 8, RULE_decision = 9, 
		RULE_id = 10;
	private static String[] makeRuleNames() {
		return new String[] {
			"start", "package_statement", "import_statement", "typestate_declaration", 
			"typestate_body", "state_declaration", "state", "method", "decision_state", 
			"decision", "id"
		};
	}
	public static final String[] ruleNames = makeRuleNames();

	private static String[] makeLiteralNames() {
		return new String[] {
			null, "'package'", "'.'", "';'", "'import'", "'*'", "'typestate'", "'{'", 
			"'}'", "'='", "','", "'('", "')'", "':'", "'<'", "'>'"
		};
	}
	private static final String[] _LITERAL_NAMES = makeLiteralNames();
	private static String[] makeSymbolicNames() {
		return new String[] {
			null, null, null, null, null, null, null, null, null, null, null, null, 
			null, null, null, null, "ID", "WS", "BlockComment", "LineComment"
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

	public static class StartContext extends ParserRuleContext {
		public TDeclarationNode ast;
		public Typestate_declarationContext t;
		public Typestate_declarationContext typestate_declaration() {
			return getRuleContext(Typestate_declarationContext.class,0);
		}
		public Package_statementContext package_statement() {
			return getRuleContext(Package_statementContext.class,0);
		}
		public List<Import_statementContext> import_statement() {
			return getRuleContexts(Import_statementContext.class);
		}
		public Import_statementContext import_statement(int i) {
			return getRuleContext(Import_statementContext.class,i);
		}
		public StartContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_start; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof TypestateListener ) ((TypestateListener)listener).enterStart(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof TypestateListener ) ((TypestateListener)listener).exitStart(this);
		}
	}

	public final StartContext start() throws RecognitionException {
		StartContext _localctx = new StartContext(_ctx, getState());
		enterRule(_localctx, 0, RULE_start);
		int _la;
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(23);
			_errHandler.sync(this);
			_la = _input.LA(1);
			if (_la==T__0) {
				{
				setState(22);
				package_statement();
				}
			}

			setState(28);
			_errHandler.sync(this);
			_la = _input.LA(1);
			while (_la==T__3) {
				{
				{
				setState(25);
				import_statement();
				}
				}
				setState(30);
				_errHandler.sync(this);
				_la = _input.LA(1);
			}
			setState(31);
			((StartContext)_localctx).t = typestate_declaration();
			((StartContext)_localctx).ast = ((StartContext)_localctx).t.ast;
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

	public static class Package_statementContext extends ParserRuleContext {
		public List<TerminalNode> ID() { return getTokens(TypestateParser.ID); }
		public TerminalNode ID(int i) {
			return getToken(TypestateParser.ID, i);
		}
		public Package_statementContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_package_statement; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof TypestateListener ) ((TypestateListener)listener).enterPackage_statement(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof TypestateListener ) ((TypestateListener)listener).exitPackage_statement(this);
		}
	}

	public final Package_statementContext package_statement() throws RecognitionException {
		Package_statementContext _localctx = new Package_statementContext(_ctx, getState());
		enterRule(_localctx, 2, RULE_package_statement);
		int _la;
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(34);
			match(T__0);
			setState(35);
			match(ID);
			setState(40);
			_errHandler.sync(this);
			_la = _input.LA(1);
			while (_la==T__1) {
				{
				{
				setState(36);
				match(T__1);
				setState(37);
				match(ID);
				}
				}
				setState(42);
				_errHandler.sync(this);
				_la = _input.LA(1);
			}
			setState(43);
			match(T__2);
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

	public static class Import_statementContext extends ParserRuleContext {
		public List<TerminalNode> ID() { return getTokens(TypestateParser.ID); }
		public TerminalNode ID(int i) {
			return getToken(TypestateParser.ID, i);
		}
		public Import_statementContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_import_statement; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof TypestateListener ) ((TypestateListener)listener).enterImport_statement(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof TypestateListener ) ((TypestateListener)listener).exitImport_statement(this);
		}
	}

	public final Import_statementContext import_statement() throws RecognitionException {
		Import_statementContext _localctx = new Import_statementContext(_ctx, getState());
		enterRule(_localctx, 4, RULE_import_statement);
		int _la;
		try {
			int _alt;
			enterOuterAlt(_localctx, 1);
			{
			setState(45);
			match(T__3);
			setState(46);
			match(ID);
			setState(51);
			_errHandler.sync(this);
			_alt = getInterpreter().adaptivePredict(_input,3,_ctx);
			while ( _alt!=2 && _alt!=org.antlr.v4.runtime.atn.ATN.INVALID_ALT_NUMBER ) {
				if ( _alt==1 ) {
					{
					{
					setState(47);
					match(T__1);
					setState(48);
					match(ID);
					}
					} 
				}
				setState(53);
				_errHandler.sync(this);
				_alt = getInterpreter().adaptivePredict(_input,3,_ctx);
			}
			setState(56);
			_errHandler.sync(this);
			_la = _input.LA(1);
			if (_la==T__1) {
				{
				setState(54);
				match(T__1);
				setState(55);
				match(T__4);
				}
			}

			setState(58);
			match(T__2);
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
		enterRule(_localctx, 6, RULE_typestate_declaration);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(60);
			((Typestate_declarationContext)_localctx).t = match(T__5);
			setState(61);
			((Typestate_declarationContext)_localctx).ID = match(ID);
			setState(62);
			match(T__6);
			setState(63);
			((Typestate_declarationContext)_localctx).typestate_body = typestate_body();
			setState(64);
			match(T__7);
			setState(65);
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
		enterRule(_localctx, 8, RULE_typestate_body);
		int _la;
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(71);
			_errHandler.sync(this);
			_la = _input.LA(1);
			while (_la==ID) {
				{
				{
				setState(68);
				((Typestate_bodyContext)_localctx).state_declaration = state_declaration();
				((Typestate_bodyContext)_localctx).s.add(((Typestate_bodyContext)_localctx).state_declaration);
				}
				}
				setState(73);
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
		enterRule(_localctx, 10, RULE_state_declaration);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(76);
			((State_declarationContext)_localctx).name = match(ID);
			setState(77);
			match(T__8);
			setState(78);
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
		enterRule(_localctx, 12, RULE_state);
		int _la;
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(81);
			((StateContext)_localctx).t = match(T__6);
			setState(90);
			_errHandler.sync(this);
			_la = _input.LA(1);
			if (_la==ID) {
				{
				setState(82);
				((StateContext)_localctx).method = method();
				((StateContext)_localctx).m.add(((StateContext)_localctx).method);
				setState(87);
				_errHandler.sync(this);
				_la = _input.LA(1);
				while (_la==T__9) {
					{
					{
					setState(83);
					match(T__9);
					setState(84);
					((StateContext)_localctx).method = method();
					((StateContext)_localctx).m.add(((StateContext)_localctx).method);
					}
					}
					setState(89);
					_errHandler.sync(this);
					_la = _input.LA(1);
				}
				}
			}

			setState(92);
			match(T__7);
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
		enterRule(_localctx, 14, RULE_method);
		int _la;
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(95);
			((MethodContext)_localctx).return_type = match(ID);
			setState(96);
			((MethodContext)_localctx).name = match(ID);
			setState(97);
			match(T__10);
			setState(106);
			_errHandler.sync(this);
			_la = _input.LA(1);
			if (_la==ID) {
				{
				setState(98);
				((MethodContext)_localctx).ID = match(ID);
				((MethodContext)_localctx).args.add(((MethodContext)_localctx).ID);
				setState(103);
				_errHandler.sync(this);
				_la = _input.LA(1);
				while (_la==T__9) {
					{
					{
					setState(99);
					match(T__9);
					setState(100);
					((MethodContext)_localctx).ID = match(ID);
					((MethodContext)_localctx).args.add(((MethodContext)_localctx).ID);
					}
					}
					setState(105);
					_errHandler.sync(this);
					_la = _input.LA(1);
				}
				}
			}

			setState(108);
			match(T__11);
			setState(109);
			match(T__12);
			setState(119);
			_errHandler.sync(this);
			switch (_input.LA(1)) {
			case ID:
				{
				setState(110);
				((MethodContext)_localctx).id = id();
				((MethodContext)_localctx).destination = ((MethodContext)_localctx).id.node;
				}
				break;
			case T__6:
				{
				setState(113);
				((MethodContext)_localctx).state = state();
				((MethodContext)_localctx).destination = ((MethodContext)_localctx).state.node;
				}
				break;
			case T__13:
				{
				setState(116);
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
		enterRule(_localctx, 16, RULE_decision_state);
		int _la;
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(123);
			((Decision_stateContext)_localctx).t = match(T__13);
			setState(124);
			((Decision_stateContext)_localctx).decision = decision();
			((Decision_stateContext)_localctx).decisions.add(((Decision_stateContext)_localctx).decision);
			setState(129);
			_errHandler.sync(this);
			_la = _input.LA(1);
			while (_la==T__9) {
				{
				{
				setState(125);
				match(T__9);
				setState(126);
				((Decision_stateContext)_localctx).decision = decision();
				((Decision_stateContext)_localctx).decisions.add(((Decision_stateContext)_localctx).decision);
				}
				}
				setState(131);
				_errHandler.sync(this);
				_la = _input.LA(1);
			}
			setState(132);
			match(T__14);
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
		enterRule(_localctx, 18, RULE_decision);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(135);
			((DecisionContext)_localctx).label = match(ID);
			setState(136);
			match(T__12);
			setState(143);
			_errHandler.sync(this);
			switch (_input.LA(1)) {
			case ID:
				{
				setState(137);
				((DecisionContext)_localctx).id = id();
				((DecisionContext)_localctx).node = new TDecisionNode(tokenToPos(((DecisionContext)_localctx).label), ((DecisionContext)_localctx).label.getText(), ((DecisionContext)_localctx).id.node);
				}
				break;
			case T__6:
				{
				setState(140);
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
		enterRule(_localctx, 20, RULE_id);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(145);
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
		"\3\u608b\ua72a\u8133\ub9ed\u417c\u3be7\u7786\u5964\3\25\u0097\4\2\t\2"+
		"\4\3\t\3\4\4\t\4\4\5\t\5\4\6\t\6\4\7\t\7\4\b\t\b\4\t\t\t\4\n\t\n\4\13"+
		"\t\13\4\f\t\f\3\2\5\2\32\n\2\3\2\7\2\35\n\2\f\2\16\2 \13\2\3\2\3\2\3\2"+
		"\3\3\3\3\3\3\3\3\7\3)\n\3\f\3\16\3,\13\3\3\3\3\3\3\4\3\4\3\4\3\4\7\4\64"+
		"\n\4\f\4\16\4\67\13\4\3\4\3\4\5\4;\n\4\3\4\3\4\3\5\3\5\3\5\3\5\3\5\3\5"+
		"\3\5\3\5\3\6\7\6H\n\6\f\6\16\6K\13\6\3\6\3\6\3\7\3\7\3\7\3\7\3\7\3\b\3"+
		"\b\3\b\3\b\7\bX\n\b\f\b\16\b[\13\b\5\b]\n\b\3\b\3\b\3\b\3\t\3\t\3\t\3"+
		"\t\3\t\3\t\7\th\n\t\f\t\16\tk\13\t\5\tm\n\t\3\t\3\t\3\t\3\t\3\t\3\t\3"+
		"\t\3\t\3\t\3\t\3\t\5\tz\n\t\3\t\3\t\3\n\3\n\3\n\3\n\7\n\u0082\n\n\f\n"+
		"\16\n\u0085\13\n\3\n\3\n\3\n\3\13\3\13\3\13\3\13\3\13\3\13\3\13\3\13\5"+
		"\13\u0092\n\13\3\f\3\f\3\f\3\f\2\2\r\2\4\6\b\n\f\16\20\22\24\26\2\2\2"+
		"\u0099\2\31\3\2\2\2\4$\3\2\2\2\6/\3\2\2\2\b>\3\2\2\2\nI\3\2\2\2\fN\3\2"+
		"\2\2\16S\3\2\2\2\20a\3\2\2\2\22}\3\2\2\2\24\u0089\3\2\2\2\26\u0093\3\2"+
		"\2\2\30\32\5\4\3\2\31\30\3\2\2\2\31\32\3\2\2\2\32\36\3\2\2\2\33\35\5\6"+
		"\4\2\34\33\3\2\2\2\35 \3\2\2\2\36\34\3\2\2\2\36\37\3\2\2\2\37!\3\2\2\2"+
		" \36\3\2\2\2!\"\5\b\5\2\"#\b\2\1\2#\3\3\2\2\2$%\7\3\2\2%*\7\22\2\2&\'"+
		"\7\4\2\2\')\7\22\2\2(&\3\2\2\2),\3\2\2\2*(\3\2\2\2*+\3\2\2\2+-\3\2\2\2"+
		",*\3\2\2\2-.\7\5\2\2.\5\3\2\2\2/\60\7\6\2\2\60\65\7\22\2\2\61\62\7\4\2"+
		"\2\62\64\7\22\2\2\63\61\3\2\2\2\64\67\3\2\2\2\65\63\3\2\2\2\65\66\3\2"+
		"\2\2\66:\3\2\2\2\67\65\3\2\2\289\7\4\2\29;\7\7\2\2:8\3\2\2\2:;\3\2\2\2"+
		";<\3\2\2\2<=\7\5\2\2=\7\3\2\2\2>?\7\b\2\2?@\7\22\2\2@A\7\t\2\2AB\5\n\6"+
		"\2BC\7\n\2\2CD\7\2\2\3DE\b\5\1\2E\t\3\2\2\2FH\5\f\7\2GF\3\2\2\2HK\3\2"+
		"\2\2IG\3\2\2\2IJ\3\2\2\2JL\3\2\2\2KI\3\2\2\2LM\b\6\1\2M\13\3\2\2\2NO\7"+
		"\22\2\2OP\7\13\2\2PQ\5\16\b\2QR\b\7\1\2R\r\3\2\2\2S\\\7\t\2\2TY\5\20\t"+
		"\2UV\7\f\2\2VX\5\20\t\2WU\3\2\2\2X[\3\2\2\2YW\3\2\2\2YZ\3\2\2\2Z]\3\2"+
		"\2\2[Y\3\2\2\2\\T\3\2\2\2\\]\3\2\2\2]^\3\2\2\2^_\7\n\2\2_`\b\b\1\2`\17"+
		"\3\2\2\2ab\7\22\2\2bc\7\22\2\2cl\7\r\2\2di\7\22\2\2ef\7\f\2\2fh\7\22\2"+
		"\2ge\3\2\2\2hk\3\2\2\2ig\3\2\2\2ij\3\2\2\2jm\3\2\2\2ki\3\2\2\2ld\3\2\2"+
		"\2lm\3\2\2\2mn\3\2\2\2no\7\16\2\2oy\7\17\2\2pq\5\26\f\2qr\b\t\1\2rz\3"+
		"\2\2\2st\5\16\b\2tu\b\t\1\2uz\3\2\2\2vw\5\22\n\2wx\b\t\1\2xz\3\2\2\2y"+
		"p\3\2\2\2ys\3\2\2\2yv\3\2\2\2z{\3\2\2\2{|\b\t\1\2|\21\3\2\2\2}~\7\20\2"+
		"\2~\u0083\5\24\13\2\177\u0080\7\f\2\2\u0080\u0082\5\24\13\2\u0081\177"+
		"\3\2\2\2\u0082\u0085\3\2\2\2\u0083\u0081\3\2\2\2\u0083\u0084\3\2\2\2\u0084"+
		"\u0086\3\2\2\2\u0085\u0083\3\2\2\2\u0086\u0087\7\21\2\2\u0087\u0088\b"+
		"\n\1\2\u0088\23\3\2\2\2\u0089\u008a\7\22\2\2\u008a\u0091\7\17\2\2\u008b"+
		"\u008c\5\26\f\2\u008c\u008d\b\13\1\2\u008d\u0092\3\2\2\2\u008e\u008f\5"+
		"\16\b\2\u008f\u0090\b\13\1\2\u0090\u0092\3\2\2\2\u0091\u008b\3\2\2\2\u0091"+
		"\u008e\3\2\2\2\u0092\25\3\2\2\2\u0093\u0094\7\22\2\2\u0094\u0095\b\f\1"+
		"\2\u0095\27\3\2\2\2\17\31\36*\65:IY\\ily\u0083\u0091";
	public static final ATN _ATN =
		new ATNDeserializer().deserialize(_serializedATN.toCharArray());
	static {
		_decisionToDFA = new DFA[_ATN.getNumberOfDecisions()];
		for (int i = 0; i < _ATN.getNumberOfDecisions(); i++) {
			_decisionToDFA[i] = new DFA(_ATN.getDecisionState(i), i);
		}
	}
}