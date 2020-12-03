// Generated from org\checkerframework\checker\jtc\typestate\parser\Typestate.g4 by ANTLR 4.8

package org.checkerframework.checker.jtc.typestate.parser;
import org.checkerframework.checker.jtc.typestate.*;
import static org.checkerframework.checker.jtc.typestate.Position.tokenToPos;
import static org.checkerframework.checker.jtc.typestate.Utils.map;

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
		T__9=10, T__10=11, T__11=12, T__12=13, T__13=14, T__14=15, T__15=16, DROP=17, 
		END=18, ID=19, WS=20, BlockComment=21, LineComment=22;
	public static final int
		RULE_start = 0, RULE_ref = 1, RULE_package_statement = 2, RULE_import_statement = 3, 
		RULE_typestate_declaration = 4, RULE_typestate_body = 5, RULE_state_declaration = 6, 
		RULE_state = 7, RULE_method = 8, RULE_decision_state = 9, RULE_decision = 10, 
		RULE_id = 11;
	private static String[] makeRuleNames() {
		return new String[] {
			"start", "ref", "package_statement", "import_statement", "typestate_declaration", 
			"typestate_body", "state_declaration", "state", "method", "decision_state", 
			"decision", "id"
		};
	}
	public static final String[] ruleNames = makeRuleNames();

	private static String[] makeLiteralNames() {
		return new String[] {
			null, "'.'", "'package'", "';'", "'import'", "'static'", "'*'", "'typestate'", 
			"'{'", "'}'", "'='", "','", "':'", "'('", "')'", "'<'", "'>'", "'drop'", 
			"'end'"
		};
	}
	private static final String[] _LITERAL_NAMES = makeLiteralNames();
	private static String[] makeSymbolicNames() {
		return new String[] {
			null, null, null, null, null, null, null, null, null, null, null, null, 
			null, null, null, null, null, "DROP", "END", "ID", "WS", "BlockComment", 
			"LineComment"
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
		public TTypestateNode ast;
		public TPackageNode pkg;
		public Package_statementContext p;
		public Import_statementContext import_statement;
		public List<Import_statementContext> i = new ArrayList<Import_statementContext>();
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
			setState(27);
			_errHandler.sync(this);
			_la = _input.LA(1);
			if (_la==T__1) {
				{
				setState(24);
				((StartContext)_localctx).p = package_statement();
				((StartContext)_localctx).pkg = ((StartContext)_localctx).p.node;
				}
			}

			setState(32);
			_errHandler.sync(this);
			_la = _input.LA(1);
			while (_la==T__3) {
				{
				{
				setState(29);
				((StartContext)_localctx).import_statement = import_statement();
				((StartContext)_localctx).i.add(((StartContext)_localctx).import_statement);
				}
				}
				setState(34);
				_errHandler.sync(this);
				_la = _input.LA(1);
			}
			setState(35);
			((StartContext)_localctx).t = typestate_declaration();
			((StartContext)_localctx).ast = new TTypestateNode(_localctx.pkg, map(((StartContext)_localctx).i, i -> i.node), ((StartContext)_localctx).t.node);
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

	public static class RefContext extends ParserRuleContext {
		public TRefNode node;
		public RefContext r;
		public IdContext id;
		public IdContext id() {
			return getRuleContext(IdContext.class,0);
		}
		public RefContext ref() {
			return getRuleContext(RefContext.class,0);
		}
		public RefContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_ref; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof TypestateListener ) ((TypestateListener)listener).enterRef(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof TypestateListener ) ((TypestateListener)listener).exitRef(this);
		}
	}

	public final RefContext ref() throws RecognitionException {
		return ref(0);
	}

	private RefContext ref(int _p) throws RecognitionException {
		ParserRuleContext _parentctx = _ctx;
		int _parentState = getState();
		RefContext _localctx = new RefContext(_ctx, _parentState);
		RefContext _prevctx = _localctx;
		int _startState = 2;
		enterRecursionRule(_localctx, 2, RULE_ref, _p);
		try {
			int _alt;
			enterOuterAlt(_localctx, 1);
			{
			{
			setState(39);
			((RefContext)_localctx).id = id();
			((RefContext)_localctx).node = ((RefContext)_localctx).id.node;
			}
			_ctx.stop = _input.LT(-1);
			setState(49);
			_errHandler.sync(this);
			_alt = getInterpreter().adaptivePredict(_input,2,_ctx);
			while ( _alt!=2 && _alt!=org.antlr.v4.runtime.atn.ATN.INVALID_ALT_NUMBER ) {
				if ( _alt==1 ) {
					if ( _parseListeners!=null ) triggerExitRuleEvent();
					_prevctx = _localctx;
					{
					{
					_localctx = new RefContext(_parentctx, _parentState);
					_localctx.r = _prevctx;
					_localctx.r = _prevctx;
					pushNewRecursionContext(_localctx, _startState, RULE_ref);
					setState(42);
					if (!(precpred(_ctx, 1))) throw new FailedPredicateException(this, "precpred(_ctx, 1)");
					setState(43);
					match(T__0);
					setState(44);
					((RefContext)_localctx).id = id();
					((RefContext)_localctx).node = new TMemberNode(((RefContext)_localctx).r.node.getPos(), ((RefContext)_localctx).r.node, ((RefContext)_localctx).id.node);
					}
					} 
				}
				setState(51);
				_errHandler.sync(this);
				_alt = getInterpreter().adaptivePredict(_input,2,_ctx);
			}
			}
		}
		catch (RecognitionException re) {
			_localctx.exception = re;
			_errHandler.reportError(this, re);
			_errHandler.recover(this, re);
		}
		finally {
			unrollRecursionContexts(_parentctx);
		}
		return _localctx;
	}

	public static class Package_statementContext extends ParserRuleContext {
		public TPackageNode node;
		public Token t;
		public RefContext ref;
		public RefContext ref() {
			return getRuleContext(RefContext.class,0);
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
		enterRule(_localctx, 4, RULE_package_statement);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(52);
			((Package_statementContext)_localctx).t = match(T__1);
			setState(53);
			((Package_statementContext)_localctx).ref = ref(0);
			setState(54);
			match(T__2);
			((Package_statementContext)_localctx).node = new TPackageNode(tokenToPos(((Package_statementContext)_localctx).t), ((Package_statementContext)_localctx).ref.node);
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
		public TImportNode node;
		public Token t;
		public Token s;
		public RefContext ref;
		public Token star;
		public RefContext ref() {
			return getRuleContext(RefContext.class,0);
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
		enterRule(_localctx, 6, RULE_import_statement);
		int _la;
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(57);
			((Import_statementContext)_localctx).t = match(T__3);
			setState(59);
			_errHandler.sync(this);
			_la = _input.LA(1);
			if (_la==T__4) {
				{
				setState(58);
				((Import_statementContext)_localctx).s = match(T__4);
				}
			}

			setState(61);
			((Import_statementContext)_localctx).ref = ref(0);
			setState(64);
			_errHandler.sync(this);
			_la = _input.LA(1);
			if (_la==T__0) {
				{
				setState(62);
				match(T__0);
				setState(63);
				((Import_statementContext)_localctx).star = match(T__5);
				}
			}

			setState(66);
			match(T__2);
			((Import_statementContext)_localctx).node = new TImportNode(tokenToPos(((Import_statementContext)_localctx).t), ((Import_statementContext)_localctx).ref.node, ((Import_statementContext)_localctx).s != null, ((Import_statementContext)_localctx).star != null);
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
		public TDeclarationNode node;
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
		enterRule(_localctx, 8, RULE_typestate_declaration);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(69);
			((Typestate_declarationContext)_localctx).t = match(T__6);
			setState(70);
			((Typestate_declarationContext)_localctx).ID = match(ID);
			setState(71);
			match(T__7);
			setState(72);
			((Typestate_declarationContext)_localctx).typestate_body = typestate_body();
			setState(73);
			match(T__8);
			setState(74);
			match(EOF);
			((Typestate_declarationContext)_localctx).node = new TDeclarationNode(tokenToPos(((Typestate_declarationContext)_localctx).t), ((Typestate_declarationContext)_localctx).ID.getText(), ((Typestate_declarationContext)_localctx).typestate_body.states);
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
		enterRule(_localctx, 10, RULE_typestate_body);
		int _la;
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(80);
			_errHandler.sync(this);
			_la = _input.LA(1);
			while (_la==ID) {
				{
				{
				setState(77);
				((Typestate_bodyContext)_localctx).state_declaration = state_declaration();
				((Typestate_bodyContext)_localctx).s.add(((Typestate_bodyContext)_localctx).state_declaration);
				}
				}
				setState(82);
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
		enterRule(_localctx, 12, RULE_state_declaration);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(85);
			((State_declarationContext)_localctx).name = match(ID);
			setState(86);
			match(T__9);
			setState(87);
			((State_declarationContext)_localctx).state = state();
			((State_declarationContext)_localctx).node = new TStateNode(tokenToPos(((State_declarationContext)_localctx).name), ((State_declarationContext)_localctx).name.getText(), ((State_declarationContext)_localctx).state.node.getMethods(), ((State_declarationContext)_localctx).state.node.isDroppable());
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
		public boolean isDroppable;
		public Token t;
		public MethodContext method;
		public List<MethodContext> m = new ArrayList<MethodContext>();
		public List<MethodContext> method() {
			return getRuleContexts(MethodContext.class);
		}
		public MethodContext method(int i) {
			return getRuleContext(MethodContext.class,i);
		}
		public TerminalNode DROP() { return getToken(TypestateParser.DROP, 0); }
		public TerminalNode END() { return getToken(TypestateParser.END, 0); }
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
		enterRule(_localctx, 14, RULE_state);
		int _la;
		try {
			int _alt;
			enterOuterAlt(_localctx, 1);
			{
			setState(90);
			((StateContext)_localctx).t = match(T__7);
			setState(106);
			_errHandler.sync(this);
			_la = _input.LA(1);
			if ((((_la) & ~0x3f) == 0 && ((1L << _la) & ((1L << DROP) | (1L << END) | (1L << ID))) != 0)) {
				{
				setState(91);
				((StateContext)_localctx).method = method();
				((StateContext)_localctx).m.add(((StateContext)_localctx).method);
				setState(96);
				_errHandler.sync(this);
				_alt = getInterpreter().adaptivePredict(_input,6,_ctx);
				while ( _alt!=2 && _alt!=org.antlr.v4.runtime.atn.ATN.INVALID_ALT_NUMBER ) {
					if ( _alt==1 ) {
						{
						{
						setState(92);
						match(T__10);
						setState(93);
						((StateContext)_localctx).method = method();
						((StateContext)_localctx).m.add(((StateContext)_localctx).method);
						}
						} 
					}
					setState(98);
					_errHandler.sync(this);
					_alt = getInterpreter().adaptivePredict(_input,6,_ctx);
				}
				setState(104);
				_errHandler.sync(this);
				_la = _input.LA(1);
				if (_la==T__10) {
					{
					setState(99);
					match(T__10);
					setState(100);
					match(DROP);
					setState(101);
					match(T__11);
					setState(102);
					match(END);
					((StateContext)_localctx).isDroppable = true;
					}
				}

				}
			}

			setState(108);
			match(T__8);
			((StateContext)_localctx).node = new TStateNode(tokenToPos(((StateContext)_localctx).t), null, map(((StateContext)_localctx).m, it -> it.node), _localctx.isDroppable);
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
		public RefContext return_type;
		public RefContext ref;
		public Token name;
		public List<RefContext> args = new ArrayList<RefContext>();
		public StateContext state;
		public Decision_stateContext decision_state;
		public List<RefContext> ref() {
			return getRuleContexts(RefContext.class);
		}
		public RefContext ref(int i) {
			return getRuleContext(RefContext.class,i);
		}
		public TerminalNode ID() { return getToken(TypestateParser.ID, 0); }
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
		enterRule(_localctx, 16, RULE_method);
		int _la;
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(111);
			((MethodContext)_localctx).return_type = ((MethodContext)_localctx).ref = ref(0);
			setState(112);
			((MethodContext)_localctx).name = match(ID);
			setState(113);
			match(T__12);
			setState(122);
			_errHandler.sync(this);
			_la = _input.LA(1);
			if ((((_la) & ~0x3f) == 0 && ((1L << _la) & ((1L << DROP) | (1L << END) | (1L << ID))) != 0)) {
				{
				setState(114);
				((MethodContext)_localctx).ref = ((MethodContext)_localctx).ref = ref(0);
				((MethodContext)_localctx).args.add(((MethodContext)_localctx).ref);
				setState(119);
				_errHandler.sync(this);
				_la = _input.LA(1);
				while (_la==T__10) {
					{
					{
					setState(115);
					match(T__10);
					setState(116);
					((MethodContext)_localctx).ref = ((MethodContext)_localctx).ref = ref(0);
					((MethodContext)_localctx).args.add(((MethodContext)_localctx).ref);
					}
					}
					setState(121);
					_errHandler.sync(this);
					_la = _input.LA(1);
				}
				}
			}

			setState(124);
			match(T__13);
			setState(125);
			match(T__11);
			setState(135);
			_errHandler.sync(this);
			switch (_input.LA(1)) {
			case DROP:
			case END:
			case ID:
				{
				setState(126);
				((MethodContext)_localctx).ref = ref(0);
				((MethodContext)_localctx).destination = ((MethodContext)_localctx).ref.node;
				}
				break;
			case T__7:
				{
				setState(129);
				((MethodContext)_localctx).state = state();
				((MethodContext)_localctx).destination = ((MethodContext)_localctx).state.node;
				}
				break;
			case T__14:
				{
				setState(132);
				((MethodContext)_localctx).decision_state = decision_state();
				((MethodContext)_localctx).destination = ((MethodContext)_localctx).decision_state.node;
				}
				break;
			default:
				throw new NoViableAltException(this);
			}
			((MethodContext)_localctx).node = new TMethodNode(((MethodContext)_localctx).return_type.node.getPos(), ((MethodContext)_localctx).return_type.node, ((MethodContext)_localctx).name.getText(), map(((MethodContext)_localctx).args, a -> a.node), _localctx.destination);
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
		enterRule(_localctx, 18, RULE_decision_state);
		int _la;
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(139);
			((Decision_stateContext)_localctx).t = match(T__14);
			setState(140);
			((Decision_stateContext)_localctx).decision = decision();
			((Decision_stateContext)_localctx).decisions.add(((Decision_stateContext)_localctx).decision);
			setState(145);
			_errHandler.sync(this);
			_la = _input.LA(1);
			while (_la==T__10) {
				{
				{
				setState(141);
				match(T__10);
				setState(142);
				((Decision_stateContext)_localctx).decision = decision();
				((Decision_stateContext)_localctx).decisions.add(((Decision_stateContext)_localctx).decision);
				}
				}
				setState(147);
				_errHandler.sync(this);
				_la = _input.LA(1);
			}
			setState(148);
			match(T__15);
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
		public RefContext ref;
		public StateContext state;
		public TerminalNode ID() { return getToken(TypestateParser.ID, 0); }
		public RefContext ref() {
			return getRuleContext(RefContext.class,0);
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
		enterRule(_localctx, 20, RULE_decision);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(151);
			((DecisionContext)_localctx).label = match(ID);
			setState(152);
			match(T__11);
			setState(159);
			_errHandler.sync(this);
			switch (_input.LA(1)) {
			case DROP:
			case END:
			case ID:
				{
				setState(153);
				((DecisionContext)_localctx).ref = ref(0);
				((DecisionContext)_localctx).node = new TDecisionNode(tokenToPos(((DecisionContext)_localctx).label), ((DecisionContext)_localctx).label.getText(), ((DecisionContext)_localctx).ref.node);
				}
				break;
			case T__7:
				{
				setState(156);
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
		public Token DROP;
		public Token END;
		public Token ID;
		public TerminalNode DROP() { return getToken(TypestateParser.DROP, 0); }
		public TerminalNode END() { return getToken(TypestateParser.END, 0); }
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
		enterRule(_localctx, 22, RULE_id);
		try {
			setState(167);
			_errHandler.sync(this);
			switch (_input.LA(1)) {
			case DROP:
				enterOuterAlt(_localctx, 1);
				{
				setState(161);
				((IdContext)_localctx).DROP = match(DROP);
				((IdContext)_localctx).node = new TIdNode(tokenToPos(((IdContext)_localctx).DROP), ((IdContext)_localctx).DROP.getText());
				}
				break;
			case END:
				enterOuterAlt(_localctx, 2);
				{
				setState(163);
				((IdContext)_localctx).END = match(END);
				((IdContext)_localctx).node = new TIdNode(tokenToPos(((IdContext)_localctx).END), ((IdContext)_localctx).END.getText());
				}
				break;
			case ID:
				enterOuterAlt(_localctx, 3);
				{
				setState(165);
				((IdContext)_localctx).ID = match(ID);
				((IdContext)_localctx).node = new TIdNode(tokenToPos(((IdContext)_localctx).ID), ((IdContext)_localctx).ID.getText());
				}
				break;
			default:
				throw new NoViableAltException(this);
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

	public boolean sempred(RuleContext _localctx, int ruleIndex, int predIndex) {
		switch (ruleIndex) {
		case 1:
			return ref_sempred((RefContext)_localctx, predIndex);
		}
		return true;
	}
	private boolean ref_sempred(RefContext _localctx, int predIndex) {
		switch (predIndex) {
		case 0:
			return precpred(_ctx, 1);
		}
		return true;
	}

	public static final String _serializedATN =
		"\3\u608b\ua72a\u8133\ub9ed\u417c\u3be7\u7786\u5964\3\30\u00ac\4\2\t\2"+
		"\4\3\t\3\4\4\t\4\4\5\t\5\4\6\t\6\4\7\t\7\4\b\t\b\4\t\t\t\4\n\t\n\4\13"+
		"\t\13\4\f\t\f\4\r\t\r\3\2\3\2\3\2\5\2\36\n\2\3\2\7\2!\n\2\f\2\16\2$\13"+
		"\2\3\2\3\2\3\2\3\3\3\3\3\3\3\3\3\3\3\3\3\3\3\3\3\3\7\3\62\n\3\f\3\16\3"+
		"\65\13\3\3\4\3\4\3\4\3\4\3\4\3\5\3\5\5\5>\n\5\3\5\3\5\3\5\5\5C\n\5\3\5"+
		"\3\5\3\5\3\6\3\6\3\6\3\6\3\6\3\6\3\6\3\6\3\7\7\7Q\n\7\f\7\16\7T\13\7\3"+
		"\7\3\7\3\b\3\b\3\b\3\b\3\b\3\t\3\t\3\t\3\t\7\ta\n\t\f\t\16\td\13\t\3\t"+
		"\3\t\3\t\3\t\3\t\5\tk\n\t\5\tm\n\t\3\t\3\t\3\t\3\n\3\n\3\n\3\n\3\n\3\n"+
		"\7\nx\n\n\f\n\16\n{\13\n\5\n}\n\n\3\n\3\n\3\n\3\n\3\n\3\n\3\n\3\n\3\n"+
		"\3\n\3\n\5\n\u008a\n\n\3\n\3\n\3\13\3\13\3\13\3\13\7\13\u0092\n\13\f\13"+
		"\16\13\u0095\13\13\3\13\3\13\3\13\3\f\3\f\3\f\3\f\3\f\3\f\3\f\3\f\5\f"+
		"\u00a2\n\f\3\r\3\r\3\r\3\r\3\r\3\r\5\r\u00aa\n\r\3\r\2\3\4\16\2\4\6\b"+
		"\n\f\16\20\22\24\26\30\2\2\2\u00b0\2\35\3\2\2\2\4(\3\2\2\2\6\66\3\2\2"+
		"\2\b;\3\2\2\2\nG\3\2\2\2\fR\3\2\2\2\16W\3\2\2\2\20\\\3\2\2\2\22q\3\2\2"+
		"\2\24\u008d\3\2\2\2\26\u0099\3\2\2\2\30\u00a9\3\2\2\2\32\33\5\6\4\2\33"+
		"\34\b\2\1\2\34\36\3\2\2\2\35\32\3\2\2\2\35\36\3\2\2\2\36\"\3\2\2\2\37"+
		"!\5\b\5\2 \37\3\2\2\2!$\3\2\2\2\" \3\2\2\2\"#\3\2\2\2#%\3\2\2\2$\"\3\2"+
		"\2\2%&\5\n\6\2&\'\b\2\1\2\'\3\3\2\2\2()\b\3\1\2)*\5\30\r\2*+\b\3\1\2+"+
		"\63\3\2\2\2,-\f\3\2\2-.\7\3\2\2./\5\30\r\2/\60\b\3\1\2\60\62\3\2\2\2\61"+
		",\3\2\2\2\62\65\3\2\2\2\63\61\3\2\2\2\63\64\3\2\2\2\64\5\3\2\2\2\65\63"+
		"\3\2\2\2\66\67\7\4\2\2\678\5\4\3\289\7\5\2\29:\b\4\1\2:\7\3\2\2\2;=\7"+
		"\6\2\2<>\7\7\2\2=<\3\2\2\2=>\3\2\2\2>?\3\2\2\2?B\5\4\3\2@A\7\3\2\2AC\7"+
		"\b\2\2B@\3\2\2\2BC\3\2\2\2CD\3\2\2\2DE\7\5\2\2EF\b\5\1\2F\t\3\2\2\2GH"+
		"\7\t\2\2HI\7\25\2\2IJ\7\n\2\2JK\5\f\7\2KL\7\13\2\2LM\7\2\2\3MN\b\6\1\2"+
		"N\13\3\2\2\2OQ\5\16\b\2PO\3\2\2\2QT\3\2\2\2RP\3\2\2\2RS\3\2\2\2SU\3\2"+
		"\2\2TR\3\2\2\2UV\b\7\1\2V\r\3\2\2\2WX\7\25\2\2XY\7\f\2\2YZ\5\20\t\2Z["+
		"\b\b\1\2[\17\3\2\2\2\\l\7\n\2\2]b\5\22\n\2^_\7\r\2\2_a\5\22\n\2`^\3\2"+
		"\2\2ad\3\2\2\2b`\3\2\2\2bc\3\2\2\2cj\3\2\2\2db\3\2\2\2ef\7\r\2\2fg\7\23"+
		"\2\2gh\7\16\2\2hi\7\24\2\2ik\b\t\1\2je\3\2\2\2jk\3\2\2\2km\3\2\2\2l]\3"+
		"\2\2\2lm\3\2\2\2mn\3\2\2\2no\7\13\2\2op\b\t\1\2p\21\3\2\2\2qr\5\4\3\2"+
		"rs\7\25\2\2s|\7\17\2\2ty\5\4\3\2uv\7\r\2\2vx\5\4\3\2wu\3\2\2\2x{\3\2\2"+
		"\2yw\3\2\2\2yz\3\2\2\2z}\3\2\2\2{y\3\2\2\2|t\3\2\2\2|}\3\2\2\2}~\3\2\2"+
		"\2~\177\7\20\2\2\177\u0089\7\16\2\2\u0080\u0081\5\4\3\2\u0081\u0082\b"+
		"\n\1\2\u0082\u008a\3\2\2\2\u0083\u0084\5\20\t\2\u0084\u0085\b\n\1\2\u0085"+
		"\u008a\3\2\2\2\u0086\u0087\5\24\13\2\u0087\u0088\b\n\1\2\u0088\u008a\3"+
		"\2\2\2\u0089\u0080\3\2\2\2\u0089\u0083\3\2\2\2\u0089\u0086\3\2\2\2\u008a"+
		"\u008b\3\2\2\2\u008b\u008c\b\n\1\2\u008c\23\3\2\2\2\u008d\u008e\7\21\2"+
		"\2\u008e\u0093\5\26\f\2\u008f\u0090\7\r\2\2\u0090\u0092\5\26\f\2\u0091"+
		"\u008f\3\2\2\2\u0092\u0095\3\2\2\2\u0093\u0091\3\2\2\2\u0093\u0094\3\2"+
		"\2\2\u0094\u0096\3\2\2\2\u0095\u0093\3\2\2\2\u0096\u0097\7\22\2\2\u0097"+
		"\u0098\b\13\1\2\u0098\25\3\2\2\2\u0099\u009a\7\25\2\2\u009a\u00a1\7\16"+
		"\2\2\u009b\u009c\5\4\3\2\u009c\u009d\b\f\1\2\u009d\u00a2\3\2\2\2\u009e"+
		"\u009f\5\20\t\2\u009f\u00a0\b\f\1\2\u00a0\u00a2\3\2\2\2\u00a1\u009b\3"+
		"\2\2\2\u00a1\u009e\3\2\2\2\u00a2\27\3\2\2\2\u00a3\u00a4\7\23\2\2\u00a4"+
		"\u00aa\b\r\1\2\u00a5\u00a6\7\24\2\2\u00a6\u00aa\b\r\1\2\u00a7\u00a8\7"+
		"\25\2\2\u00a8\u00aa\b\r\1\2\u00a9\u00a3\3\2\2\2\u00a9\u00a5\3\2\2\2\u00a9"+
		"\u00a7\3\2\2\2\u00aa\31\3\2\2\2\21\35\"\63=BRbjly|\u0089\u0093\u00a1\u00a9";
	public static final ATN _ATN =
		new ATNDeserializer().deserialize(_serializedATN.toCharArray());
	static {
		_decisionToDFA = new DFA[_ATN.getNumberOfDecisions()];
		for (int i = 0; i < _ATN.getNumberOfDecisions(); i++) {
			_decisionToDFA[i] = new DFA(_ATN.getDecisionState(i), i);
		}
	}
}