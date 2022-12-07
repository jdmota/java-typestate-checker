// Generated from java-escape by ANTLR 4.11.1

package jatyc.typestate.parser;
import jatyc.typestate.*;
import static jatyc.typestate.Position.tokenToPos;
import static jatyc.typestate.Utils.map;

import org.antlr.v4.runtime.atn.*;
import org.antlr.v4.runtime.dfa.DFA;
import org.antlr.v4.runtime.*;
import org.antlr.v4.runtime.misc.*;
import org.antlr.v4.runtime.tree.*;
import java.util.List;
import java.util.Iterator;
import java.util.ArrayList;

@SuppressWarnings({"all", "warnings", "unchecked", "unused", "cast", "CheckReturnValue"})
public class TypestateParser extends Parser {
	static { RuntimeMetaData.checkVersion("4.11.1", RuntimeMetaData.VERSION); }

	protected static final DFA[] _decisionToDFA;
	protected static final PredictionContextCache _sharedContextCache =
		new PredictionContextCache();
	public static final int
		T__0=1, T__1=2, T__2=3, T__3=4, T__4=5, T__5=6, T__6=7, T__7=8, T__8=9, 
		T__9=10, T__10=11, T__11=12, T__12=13, T__13=14, T__14=15, T__15=16, T__16=17, 
		DROP=18, END=19, ID=20, WS=21, BlockComment=22, LineComment=23;
	public static final int
		RULE_start = 0, RULE_ref = 1, RULE_javaType = 2, RULE_package_statement = 3, 
		RULE_import_statement = 4, RULE_typestate_declaration = 5, RULE_typestate_body = 6, 
		RULE_state_declaration = 7, RULE_state = 8, RULE_method = 9, RULE_decision_state = 10, 
		RULE_decision = 11, RULE_id = 12;
	private static String[] makeRuleNames() {
		return new String[] {
			"start", "ref", "javaType", "package_statement", "import_statement", 
			"typestate_declaration", "typestate_body", "state_declaration", "state", 
			"method", "decision_state", "decision", "id"
		};
	}
	public static final String[] ruleNames = makeRuleNames();

	private static String[] makeLiteralNames() {
		return new String[] {
			null, "'.'", "'[]'", "'package'", "';'", "'import'", "'static'", "'*'", 
			"'typestate'", "'{'", "'}'", "'='", "','", "':'", "'('", "')'", "'<'", 
			"'>'", "'drop'", "'end'"
		};
	}
	private static final String[] _LITERAL_NAMES = makeLiteralNames();
	private static String[] makeSymbolicNames() {
		return new String[] {
			null, null, null, null, null, null, null, null, null, null, null, null, 
			null, null, null, null, null, null, "DROP", "END", "ID", "WS", "BlockComment", 
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
	public String getGrammarFileName() { return "java-escape"; }

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

	@SuppressWarnings("CheckReturnValue")
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
			setState(29);
			_errHandler.sync(this);
			_la = _input.LA(1);
			if (_la==T__2) {
				{
				setState(26);
				((StartContext)_localctx).p = package_statement();
				((StartContext)_localctx).pkg = ((StartContext)_localctx).p.node;
				}
			}

			setState(34);
			_errHandler.sync(this);
			_la = _input.LA(1);
			while (_la==T__4) {
				{
				{
				setState(31);
				((StartContext)_localctx).import_statement = import_statement();
				((StartContext)_localctx).i.add(((StartContext)_localctx).import_statement);
				}
				}
				setState(36);
				_errHandler.sync(this);
				_la = _input.LA(1);
			}
			setState(37);
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

	@SuppressWarnings("CheckReturnValue")
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
			setState(41);
			((RefContext)_localctx).id = id();
			((RefContext)_localctx).node = ((RefContext)_localctx).id.node;
			}
			_ctx.stop = _input.LT(-1);
			setState(51);
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
					pushNewRecursionContext(_localctx, _startState, RULE_ref);
					setState(44);
					if (!(precpred(_ctx, 1))) throw new FailedPredicateException(this, "precpred(_ctx, 1)");
					setState(45);
					match(T__0);
					setState(46);
					((RefContext)_localctx).id = id();
					((RefContext)_localctx).node = new TMemberNode(((RefContext)_localctx).r.node.getPos(), ((RefContext)_localctx).r.node, ((RefContext)_localctx).id.node);
					}
					} 
				}
				setState(53);
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

	@SuppressWarnings("CheckReturnValue")
	public static class JavaTypeContext extends ParserRuleContext {
		public TRefNode node;
		public JavaTypeContext j;
		public RefContext ref;
		public RefContext ref() {
			return getRuleContext(RefContext.class,0);
		}
		public JavaTypeContext javaType() {
			return getRuleContext(JavaTypeContext.class,0);
		}
		public JavaTypeContext(ParserRuleContext parent, int invokingState) {
			super(parent, invokingState);
		}
		@Override public int getRuleIndex() { return RULE_javaType; }
		@Override
		public void enterRule(ParseTreeListener listener) {
			if ( listener instanceof TypestateListener ) ((TypestateListener)listener).enterJavaType(this);
		}
		@Override
		public void exitRule(ParseTreeListener listener) {
			if ( listener instanceof TypestateListener ) ((TypestateListener)listener).exitJavaType(this);
		}
	}

	public final JavaTypeContext javaType() throws RecognitionException {
		return javaType(0);
	}

	private JavaTypeContext javaType(int _p) throws RecognitionException {
		ParserRuleContext _parentctx = _ctx;
		int _parentState = getState();
		JavaTypeContext _localctx = new JavaTypeContext(_ctx, _parentState);
		JavaTypeContext _prevctx = _localctx;
		int _startState = 4;
		enterRecursionRule(_localctx, 4, RULE_javaType, _p);
		try {
			int _alt;
			enterOuterAlt(_localctx, 1);
			{
			{
			setState(55);
			((JavaTypeContext)_localctx).ref = ref(0);
			((JavaTypeContext)_localctx).node = ((JavaTypeContext)_localctx).ref.node;
			}
			_ctx.stop = _input.LT(-1);
			setState(63);
			_errHandler.sync(this);
			_alt = getInterpreter().adaptivePredict(_input,3,_ctx);
			while ( _alt!=2 && _alt!=org.antlr.v4.runtime.atn.ATN.INVALID_ALT_NUMBER ) {
				if ( _alt==1 ) {
					if ( _parseListeners!=null ) triggerExitRuleEvent();
					_prevctx = _localctx;
					{
					{
					_localctx = new JavaTypeContext(_parentctx, _parentState);
					_localctx.j = _prevctx;
					pushNewRecursionContext(_localctx, _startState, RULE_javaType);
					setState(58);
					if (!(precpred(_ctx, 1))) throw new FailedPredicateException(this, "precpred(_ctx, 1)");
					setState(59);
					match(T__1);
					((JavaTypeContext)_localctx).node = new TArrayTypeNode(((JavaTypeContext)_localctx).j.node.getPos(), ((JavaTypeContext)_localctx).j.node);
					}
					} 
				}
				setState(65);
				_errHandler.sync(this);
				_alt = getInterpreter().adaptivePredict(_input,3,_ctx);
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

	@SuppressWarnings("CheckReturnValue")
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
		enterRule(_localctx, 6, RULE_package_statement);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(66);
			((Package_statementContext)_localctx).t = match(T__2);
			setState(67);
			((Package_statementContext)_localctx).ref = ref(0);
			setState(68);
			match(T__3);
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

	@SuppressWarnings("CheckReturnValue")
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
		enterRule(_localctx, 8, RULE_import_statement);
		int _la;
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(71);
			((Import_statementContext)_localctx).t = match(T__4);
			setState(73);
			_errHandler.sync(this);
			_la = _input.LA(1);
			if (_la==T__5) {
				{
				setState(72);
				((Import_statementContext)_localctx).s = match(T__5);
				}
			}

			setState(75);
			((Import_statementContext)_localctx).ref = ref(0);
			setState(78);
			_errHandler.sync(this);
			_la = _input.LA(1);
			if (_la==T__0) {
				{
				setState(76);
				match(T__0);
				setState(77);
				((Import_statementContext)_localctx).star = match(T__6);
				}
			}

			setState(80);
			match(T__3);
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

	@SuppressWarnings("CheckReturnValue")
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
		enterRule(_localctx, 10, RULE_typestate_declaration);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(83);
			((Typestate_declarationContext)_localctx).t = match(T__7);
			setState(84);
			((Typestate_declarationContext)_localctx).ID = match(ID);
			setState(85);
			match(T__8);
			setState(86);
			((Typestate_declarationContext)_localctx).typestate_body = typestate_body();
			setState(87);
			match(T__9);
			setState(88);
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

	@SuppressWarnings("CheckReturnValue")
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
		enterRule(_localctx, 12, RULE_typestate_body);
		int _la;
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(94);
			_errHandler.sync(this);
			_la = _input.LA(1);
			while (_la==ID) {
				{
				{
				setState(91);
				((Typestate_bodyContext)_localctx).state_declaration = state_declaration();
				((Typestate_bodyContext)_localctx).s.add(((Typestate_bodyContext)_localctx).state_declaration);
				}
				}
				setState(96);
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

	@SuppressWarnings("CheckReturnValue")
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
		enterRule(_localctx, 14, RULE_state_declaration);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(99);
			((State_declarationContext)_localctx).name = match(ID);
			setState(100);
			match(T__10);
			setState(101);
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

	@SuppressWarnings("CheckReturnValue")
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
		enterRule(_localctx, 16, RULE_state);
		int _la;
		try {
			int _alt;
			enterOuterAlt(_localctx, 1);
			{
			setState(104);
			((StateContext)_localctx).t = match(T__8);
			setState(120);
			_errHandler.sync(this);
			_la = _input.LA(1);
			if (((_la) & ~0x3f) == 0 && ((1L << _la) & 1835008L) != 0) {
				{
				setState(105);
				((StateContext)_localctx).method = method();
				((StateContext)_localctx).m.add(((StateContext)_localctx).method);
				setState(110);
				_errHandler.sync(this);
				_alt = getInterpreter().adaptivePredict(_input,7,_ctx);
				while ( _alt!=2 && _alt!=org.antlr.v4.runtime.atn.ATN.INVALID_ALT_NUMBER ) {
					if ( _alt==1 ) {
						{
						{
						setState(106);
						match(T__11);
						setState(107);
						((StateContext)_localctx).method = method();
						((StateContext)_localctx).m.add(((StateContext)_localctx).method);
						}
						} 
					}
					setState(112);
					_errHandler.sync(this);
					_alt = getInterpreter().adaptivePredict(_input,7,_ctx);
				}
				setState(118);
				_errHandler.sync(this);
				_la = _input.LA(1);
				if (_la==T__11) {
					{
					setState(113);
					match(T__11);
					setState(114);
					match(DROP);
					setState(115);
					match(T__12);
					setState(116);
					match(END);
					((StateContext)_localctx).isDroppable = true;
					}
				}

				}
			}

			setState(122);
			match(T__9);
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

	@SuppressWarnings("CheckReturnValue")
	public static class MethodContext extends ParserRuleContext {
		public TMethodNode node;
		public TNode destination;
		public JavaTypeContext return_type;
		public Token name;
		public JavaTypeContext javaType;
		public List<JavaTypeContext> args = new ArrayList<JavaTypeContext>();
		public IdContext id;
		public StateContext state;
		public Decision_stateContext decision_state;
		public List<JavaTypeContext> javaType() {
			return getRuleContexts(JavaTypeContext.class);
		}
		public JavaTypeContext javaType(int i) {
			return getRuleContext(JavaTypeContext.class,i);
		}
		public TerminalNode ID() { return getToken(TypestateParser.ID, 0); }
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
		enterRule(_localctx, 18, RULE_method);
		int _la;
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(125);
			((MethodContext)_localctx).return_type = javaType(0);
			setState(126);
			((MethodContext)_localctx).name = match(ID);
			setState(127);
			match(T__13);
			setState(136);
			_errHandler.sync(this);
			_la = _input.LA(1);
			if (((_la) & ~0x3f) == 0 && ((1L << _la) & 1835008L) != 0) {
				{
				setState(128);
				((MethodContext)_localctx).javaType = javaType(0);
				((MethodContext)_localctx).args.add(((MethodContext)_localctx).javaType);
				setState(133);
				_errHandler.sync(this);
				_la = _input.LA(1);
				while (_la==T__11) {
					{
					{
					setState(129);
					match(T__11);
					setState(130);
					((MethodContext)_localctx).javaType = javaType(0);
					((MethodContext)_localctx).args.add(((MethodContext)_localctx).javaType);
					}
					}
					setState(135);
					_errHandler.sync(this);
					_la = _input.LA(1);
				}
				}
			}

			setState(138);
			match(T__14);
			setState(139);
			match(T__12);
			setState(149);
			_errHandler.sync(this);
			switch (_input.LA(1)) {
			case DROP:
			case END:
			case ID:
				{
				setState(140);
				((MethodContext)_localctx).id = id();
				((MethodContext)_localctx).destination = ((MethodContext)_localctx).id.node;
				}
				break;
			case T__8:
				{
				setState(143);
				((MethodContext)_localctx).state = state();
				((MethodContext)_localctx).destination = ((MethodContext)_localctx).state.node;
				}
				break;
			case T__15:
				{
				setState(146);
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

	@SuppressWarnings("CheckReturnValue")
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
		enterRule(_localctx, 20, RULE_decision_state);
		int _la;
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(153);
			((Decision_stateContext)_localctx).t = match(T__15);
			setState(154);
			((Decision_stateContext)_localctx).decision = decision();
			((Decision_stateContext)_localctx).decisions.add(((Decision_stateContext)_localctx).decision);
			setState(159);
			_errHandler.sync(this);
			_la = _input.LA(1);
			while (_la==T__11) {
				{
				{
				setState(155);
				match(T__11);
				setState(156);
				((Decision_stateContext)_localctx).decision = decision();
				((Decision_stateContext)_localctx).decisions.add(((Decision_stateContext)_localctx).decision);
				}
				}
				setState(161);
				_errHandler.sync(this);
				_la = _input.LA(1);
			}
			setState(162);
			match(T__16);
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

	@SuppressWarnings("CheckReturnValue")
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
		enterRule(_localctx, 22, RULE_decision);
		try {
			enterOuterAlt(_localctx, 1);
			{
			setState(165);
			((DecisionContext)_localctx).label = match(ID);
			setState(166);
			match(T__12);
			setState(173);
			_errHandler.sync(this);
			switch (_input.LA(1)) {
			case DROP:
			case END:
			case ID:
				{
				setState(167);
				((DecisionContext)_localctx).ref = ref(0);
				((DecisionContext)_localctx).node = new TDecisionNode(tokenToPos(((DecisionContext)_localctx).label), ((DecisionContext)_localctx).label.getText(), ((DecisionContext)_localctx).ref.node);
				}
				break;
			case T__8:
				{
				setState(170);
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

	@SuppressWarnings("CheckReturnValue")
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
		enterRule(_localctx, 24, RULE_id);
		try {
			setState(181);
			_errHandler.sync(this);
			switch (_input.LA(1)) {
			case DROP:
				enterOuterAlt(_localctx, 1);
				{
				setState(175);
				((IdContext)_localctx).DROP = match(DROP);
				((IdContext)_localctx).node = new TIdNode(tokenToPos(((IdContext)_localctx).DROP), ((IdContext)_localctx).DROP.getText());
				}
				break;
			case END:
				enterOuterAlt(_localctx, 2);
				{
				setState(177);
				((IdContext)_localctx).END = match(END);
				((IdContext)_localctx).node = new TIdNode(tokenToPos(((IdContext)_localctx).END), ((IdContext)_localctx).END.getText());
				}
				break;
			case ID:
				enterOuterAlt(_localctx, 3);
				{
				setState(179);
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
		case 2:
			return javaType_sempred((JavaTypeContext)_localctx, predIndex);
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
	private boolean javaType_sempred(JavaTypeContext _localctx, int predIndex) {
		switch (predIndex) {
		case 1:
			return precpred(_ctx, 1);
		}
		return true;
	}

	public static final String _serializedATN =
		"\u0004\u0001\u0017\u00b8\u0002\u0000\u0007\u0000\u0002\u0001\u0007\u0001"+
		"\u0002\u0002\u0007\u0002\u0002\u0003\u0007\u0003\u0002\u0004\u0007\u0004"+
		"\u0002\u0005\u0007\u0005\u0002\u0006\u0007\u0006\u0002\u0007\u0007\u0007"+
		"\u0002\b\u0007\b\u0002\t\u0007\t\u0002\n\u0007\n\u0002\u000b\u0007\u000b"+
		"\u0002\f\u0007\f\u0001\u0000\u0001\u0000\u0001\u0000\u0003\u0000\u001e"+
		"\b\u0000\u0001\u0000\u0005\u0000!\b\u0000\n\u0000\f\u0000$\t\u0000\u0001"+
		"\u0000\u0001\u0000\u0001\u0000\u0001\u0001\u0001\u0001\u0001\u0001\u0001"+
		"\u0001\u0001\u0001\u0001\u0001\u0001\u0001\u0001\u0001\u0001\u0001\u0005"+
		"\u00012\b\u0001\n\u0001\f\u00015\t\u0001\u0001\u0002\u0001\u0002\u0001"+
		"\u0002\u0001\u0002\u0001\u0002\u0001\u0002\u0001\u0002\u0005\u0002>\b"+
		"\u0002\n\u0002\f\u0002A\t\u0002\u0001\u0003\u0001\u0003\u0001\u0003\u0001"+
		"\u0003\u0001\u0003\u0001\u0004\u0001\u0004\u0003\u0004J\b\u0004\u0001"+
		"\u0004\u0001\u0004\u0001\u0004\u0003\u0004O\b\u0004\u0001\u0004\u0001"+
		"\u0004\u0001\u0004\u0001\u0005\u0001\u0005\u0001\u0005\u0001\u0005\u0001"+
		"\u0005\u0001\u0005\u0001\u0005\u0001\u0005\u0001\u0006\u0005\u0006]\b"+
		"\u0006\n\u0006\f\u0006`\t\u0006\u0001\u0006\u0001\u0006\u0001\u0007\u0001"+
		"\u0007\u0001\u0007\u0001\u0007\u0001\u0007\u0001\b\u0001\b\u0001\b\u0001"+
		"\b\u0005\bm\b\b\n\b\f\bp\t\b\u0001\b\u0001\b\u0001\b\u0001\b\u0001\b\u0003"+
		"\bw\b\b\u0003\by\b\b\u0001\b\u0001\b\u0001\b\u0001\t\u0001\t\u0001\t\u0001"+
		"\t\u0001\t\u0001\t\u0005\t\u0084\b\t\n\t\f\t\u0087\t\t\u0003\t\u0089\b"+
		"\t\u0001\t\u0001\t\u0001\t\u0001\t\u0001\t\u0001\t\u0001\t\u0001\t\u0001"+
		"\t\u0001\t\u0001\t\u0003\t\u0096\b\t\u0001\t\u0001\t\u0001\n\u0001\n\u0001"+
		"\n\u0001\n\u0005\n\u009e\b\n\n\n\f\n\u00a1\t\n\u0001\n\u0001\n\u0001\n"+
		"\u0001\u000b\u0001\u000b\u0001\u000b\u0001\u000b\u0001\u000b\u0001\u000b"+
		"\u0001\u000b\u0001\u000b\u0003\u000b\u00ae\b\u000b\u0001\f\u0001\f\u0001"+
		"\f\u0001\f\u0001\f\u0001\f\u0003\f\u00b6\b\f\u0001\f\u0000\u0002\u0002"+
		"\u0004\r\u0000\u0002\u0004\u0006\b\n\f\u000e\u0010\u0012\u0014\u0016\u0018"+
		"\u0000\u0000\u00bc\u0000\u001d\u0001\u0000\u0000\u0000\u0002(\u0001\u0000"+
		"\u0000\u0000\u00046\u0001\u0000\u0000\u0000\u0006B\u0001\u0000\u0000\u0000"+
		"\bG\u0001\u0000\u0000\u0000\nS\u0001\u0000\u0000\u0000\f^\u0001\u0000"+
		"\u0000\u0000\u000ec\u0001\u0000\u0000\u0000\u0010h\u0001\u0000\u0000\u0000"+
		"\u0012}\u0001\u0000\u0000\u0000\u0014\u0099\u0001\u0000\u0000\u0000\u0016"+
		"\u00a5\u0001\u0000\u0000\u0000\u0018\u00b5\u0001\u0000\u0000\u0000\u001a"+
		"\u001b\u0003\u0006\u0003\u0000\u001b\u001c\u0006\u0000\uffff\uffff\u0000"+
		"\u001c\u001e\u0001\u0000\u0000\u0000\u001d\u001a\u0001\u0000\u0000\u0000"+
		"\u001d\u001e\u0001\u0000\u0000\u0000\u001e\"\u0001\u0000\u0000\u0000\u001f"+
		"!\u0003\b\u0004\u0000 \u001f\u0001\u0000\u0000\u0000!$\u0001\u0000\u0000"+
		"\u0000\" \u0001\u0000\u0000\u0000\"#\u0001\u0000\u0000\u0000#%\u0001\u0000"+
		"\u0000\u0000$\"\u0001\u0000\u0000\u0000%&\u0003\n\u0005\u0000&\'\u0006"+
		"\u0000\uffff\uffff\u0000\'\u0001\u0001\u0000\u0000\u0000()\u0006\u0001"+
		"\uffff\uffff\u0000)*\u0003\u0018\f\u0000*+\u0006\u0001\uffff\uffff\u0000"+
		"+3\u0001\u0000\u0000\u0000,-\n\u0001\u0000\u0000-.\u0005\u0001\u0000\u0000"+
		"./\u0003\u0018\f\u0000/0\u0006\u0001\uffff\uffff\u000002\u0001\u0000\u0000"+
		"\u00001,\u0001\u0000\u0000\u000025\u0001\u0000\u0000\u000031\u0001\u0000"+
		"\u0000\u000034\u0001\u0000\u0000\u00004\u0003\u0001\u0000\u0000\u0000"+
		"53\u0001\u0000\u0000\u000067\u0006\u0002\uffff\uffff\u000078\u0003\u0002"+
		"\u0001\u000089\u0006\u0002\uffff\uffff\u00009?\u0001\u0000\u0000\u0000"+
		":;\n\u0001\u0000\u0000;<\u0005\u0002\u0000\u0000<>\u0006\u0002\uffff\uffff"+
		"\u0000=:\u0001\u0000\u0000\u0000>A\u0001\u0000\u0000\u0000?=\u0001\u0000"+
		"\u0000\u0000?@\u0001\u0000\u0000\u0000@\u0005\u0001\u0000\u0000\u0000"+
		"A?\u0001\u0000\u0000\u0000BC\u0005\u0003\u0000\u0000CD\u0003\u0002\u0001"+
		"\u0000DE\u0005\u0004\u0000\u0000EF\u0006\u0003\uffff\uffff\u0000F\u0007"+
		"\u0001\u0000\u0000\u0000GI\u0005\u0005\u0000\u0000HJ\u0005\u0006\u0000"+
		"\u0000IH\u0001\u0000\u0000\u0000IJ\u0001\u0000\u0000\u0000JK\u0001\u0000"+
		"\u0000\u0000KN\u0003\u0002\u0001\u0000LM\u0005\u0001\u0000\u0000MO\u0005"+
		"\u0007\u0000\u0000NL\u0001\u0000\u0000\u0000NO\u0001\u0000\u0000\u0000"+
		"OP\u0001\u0000\u0000\u0000PQ\u0005\u0004\u0000\u0000QR\u0006\u0004\uffff"+
		"\uffff\u0000R\t\u0001\u0000\u0000\u0000ST\u0005\b\u0000\u0000TU\u0005"+
		"\u0014\u0000\u0000UV\u0005\t\u0000\u0000VW\u0003\f\u0006\u0000WX\u0005"+
		"\n\u0000\u0000XY\u0005\u0000\u0000\u0001YZ\u0006\u0005\uffff\uffff\u0000"+
		"Z\u000b\u0001\u0000\u0000\u0000[]\u0003\u000e\u0007\u0000\\[\u0001\u0000"+
		"\u0000\u0000]`\u0001\u0000\u0000\u0000^\\\u0001\u0000\u0000\u0000^_\u0001"+
		"\u0000\u0000\u0000_a\u0001\u0000\u0000\u0000`^\u0001\u0000\u0000\u0000"+
		"ab\u0006\u0006\uffff\uffff\u0000b\r\u0001\u0000\u0000\u0000cd\u0005\u0014"+
		"\u0000\u0000de\u0005\u000b\u0000\u0000ef\u0003\u0010\b\u0000fg\u0006\u0007"+
		"\uffff\uffff\u0000g\u000f\u0001\u0000\u0000\u0000hx\u0005\t\u0000\u0000"+
		"in\u0003\u0012\t\u0000jk\u0005\f\u0000\u0000km\u0003\u0012\t\u0000lj\u0001"+
		"\u0000\u0000\u0000mp\u0001\u0000\u0000\u0000nl\u0001\u0000\u0000\u0000"+
		"no\u0001\u0000\u0000\u0000ov\u0001\u0000\u0000\u0000pn\u0001\u0000\u0000"+
		"\u0000qr\u0005\f\u0000\u0000rs\u0005\u0012\u0000\u0000st\u0005\r\u0000"+
		"\u0000tu\u0005\u0013\u0000\u0000uw\u0006\b\uffff\uffff\u0000vq\u0001\u0000"+
		"\u0000\u0000vw\u0001\u0000\u0000\u0000wy\u0001\u0000\u0000\u0000xi\u0001"+
		"\u0000\u0000\u0000xy\u0001\u0000\u0000\u0000yz\u0001\u0000\u0000\u0000"+
		"z{\u0005\n\u0000\u0000{|\u0006\b\uffff\uffff\u0000|\u0011\u0001\u0000"+
		"\u0000\u0000}~\u0003\u0004\u0002\u0000~\u007f\u0005\u0014\u0000\u0000"+
		"\u007f\u0088\u0005\u000e\u0000\u0000\u0080\u0085\u0003\u0004\u0002\u0000"+
		"\u0081\u0082\u0005\f\u0000\u0000\u0082\u0084\u0003\u0004\u0002\u0000\u0083"+
		"\u0081\u0001\u0000\u0000\u0000\u0084\u0087\u0001\u0000\u0000\u0000\u0085"+
		"\u0083\u0001\u0000\u0000\u0000\u0085\u0086\u0001\u0000\u0000\u0000\u0086"+
		"\u0089\u0001\u0000\u0000\u0000\u0087\u0085\u0001\u0000\u0000\u0000\u0088"+
		"\u0080\u0001\u0000\u0000\u0000\u0088\u0089\u0001\u0000\u0000\u0000\u0089"+
		"\u008a\u0001\u0000\u0000\u0000\u008a\u008b\u0005\u000f\u0000\u0000\u008b"+
		"\u0095\u0005\r\u0000\u0000\u008c\u008d\u0003\u0018\f\u0000\u008d\u008e"+
		"\u0006\t\uffff\uffff\u0000\u008e\u0096\u0001\u0000\u0000\u0000\u008f\u0090"+
		"\u0003\u0010\b\u0000\u0090\u0091\u0006\t\uffff\uffff\u0000\u0091\u0096"+
		"\u0001\u0000\u0000\u0000\u0092\u0093\u0003\u0014\n\u0000\u0093\u0094\u0006"+
		"\t\uffff\uffff\u0000\u0094\u0096\u0001\u0000\u0000\u0000\u0095\u008c\u0001"+
		"\u0000\u0000\u0000\u0095\u008f\u0001\u0000\u0000\u0000\u0095\u0092\u0001"+
		"\u0000\u0000\u0000\u0096\u0097\u0001\u0000\u0000\u0000\u0097\u0098\u0006"+
		"\t\uffff\uffff\u0000\u0098\u0013\u0001\u0000\u0000\u0000\u0099\u009a\u0005"+
		"\u0010\u0000\u0000\u009a\u009f\u0003\u0016\u000b\u0000\u009b\u009c\u0005"+
		"\f\u0000\u0000\u009c\u009e\u0003\u0016\u000b\u0000\u009d\u009b\u0001\u0000"+
		"\u0000\u0000\u009e\u00a1\u0001\u0000\u0000\u0000\u009f\u009d\u0001\u0000"+
		"\u0000\u0000\u009f\u00a0\u0001\u0000\u0000\u0000\u00a0\u00a2\u0001\u0000"+
		"\u0000\u0000\u00a1\u009f\u0001\u0000\u0000\u0000\u00a2\u00a3\u0005\u0011"+
		"\u0000\u0000\u00a3\u00a4\u0006\n\uffff\uffff\u0000\u00a4\u0015\u0001\u0000"+
		"\u0000\u0000\u00a5\u00a6\u0005\u0014\u0000\u0000\u00a6\u00ad\u0005\r\u0000"+
		"\u0000\u00a7\u00a8\u0003\u0002\u0001\u0000\u00a8\u00a9\u0006\u000b\uffff"+
		"\uffff\u0000\u00a9\u00ae\u0001\u0000\u0000\u0000\u00aa\u00ab\u0003\u0010"+
		"\b\u0000\u00ab\u00ac\u0006\u000b\uffff\uffff\u0000\u00ac\u00ae\u0001\u0000"+
		"\u0000\u0000\u00ad\u00a7\u0001\u0000\u0000\u0000\u00ad\u00aa\u0001\u0000"+
		"\u0000\u0000\u00ae\u0017\u0001\u0000\u0000\u0000\u00af\u00b0\u0005\u0012"+
		"\u0000\u0000\u00b0\u00b6\u0006\f\uffff\uffff\u0000\u00b1\u00b2\u0005\u0013"+
		"\u0000\u0000\u00b2\u00b6\u0006\f\uffff\uffff\u0000\u00b3\u00b4\u0005\u0014"+
		"\u0000\u0000\u00b4\u00b6\u0006\f\uffff\uffff\u0000\u00b5\u00af\u0001\u0000"+
		"\u0000\u0000\u00b5\u00b1\u0001\u0000\u0000\u0000\u00b5\u00b3\u0001\u0000"+
		"\u0000\u0000\u00b6\u0019\u0001\u0000\u0000\u0000\u0010\u001d\"3?IN^nv"+
		"x\u0085\u0088\u0095\u009f\u00ad\u00b5";
	public static final ATN _ATN =
		new ATNDeserializer().deserialize(_serializedATN.toCharArray());
	static {
		_decisionToDFA = new DFA[_ATN.getNumberOfDecisions()];
		for (int i = 0; i < _ATN.getNumberOfDecisions(); i++) {
			_decisionToDFA[i] = new DFA(_ATN.getDecisionState(i), i);
		}
	}
}