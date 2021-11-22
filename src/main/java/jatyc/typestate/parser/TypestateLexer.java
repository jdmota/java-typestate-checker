// Generated from jatyc\typestate\parser\Typestate.g4 by ANTLR 4.8

package jatyc.typestate.parser;
import jatyc.typestate.*;
import static jatyc.typestate.Position.tokenToPos;
import static jatyc.typestate.Utils.map;

import org.antlr.v4.runtime.Lexer;
import org.antlr.v4.runtime.CharStream;
import org.antlr.v4.runtime.Token;
import org.antlr.v4.runtime.TokenStream;
import org.antlr.v4.runtime.*;
import org.antlr.v4.runtime.atn.*;
import org.antlr.v4.runtime.dfa.DFA;
import org.antlr.v4.runtime.misc.*;

@SuppressWarnings({"all", "warnings", "unchecked", "unused", "cast"})
public class TypestateLexer extends Lexer {
	static { RuntimeMetaData.checkVersion("4.8", RuntimeMetaData.VERSION); }

	protected static final DFA[] _decisionToDFA;
	protected static final PredictionContextCache _sharedContextCache =
		new PredictionContextCache();
	public static final int
		T__0=1, T__1=2, T__2=3, T__3=4, T__4=5, T__5=6, T__6=7, T__7=8, T__8=9, 
		T__9=10, T__10=11, T__11=12, T__12=13, T__13=14, T__14=15, T__15=16, T__16=17, 
		DROP=18, END=19, ID=20, WS=21, BlockComment=22, LineComment=23;
	public static String[] channelNames = {
		"DEFAULT_TOKEN_CHANNEL", "HIDDEN"
	};

	public static String[] modeNames = {
		"DEFAULT_MODE"
	};

	private static String[] makeRuleNames() {
		return new String[] {
			"T__0", "T__1", "T__2", "T__3", "T__4", "T__5", "T__6", "T__7", "T__8", 
			"T__9", "T__10", "T__11", "T__12", "T__13", "T__14", "T__15", "T__16", 
			"DROP", "END", "ID", "WS", "BlockComment", "LineComment"
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


	public TypestateLexer(CharStream input) {
		super(input);
		_interp = new LexerATNSimulator(this,_ATN,_decisionToDFA,_sharedContextCache);
	}

	@Override
	public String getGrammarFileName() { return "Typestate.g4"; }

	@Override
	public String[] getRuleNames() { return ruleNames; }

	@Override
	public String getSerializedATN() { return _serializedATN; }

	@Override
	public String[] getChannelNames() { return channelNames; }

	@Override
	public String[] getModeNames() { return modeNames; }

	@Override
	public ATN getATN() { return _ATN; }

	public static final String _serializedATN =
		"\3\u608b\ua72a\u8133\ub9ed\u417c\u3be7\u7786\u5964\2\31\u00a0\b\1\4\2"+
		"\t\2\4\3\t\3\4\4\t\4\4\5\t\5\4\6\t\6\4\7\t\7\4\b\t\b\4\t\t\t\4\n\t\n\4"+
		"\13\t\13\4\f\t\f\4\r\t\r\4\16\t\16\4\17\t\17\4\20\t\20\4\21\t\21\4\22"+
		"\t\22\4\23\t\23\4\24\t\24\4\25\t\25\4\26\t\26\4\27\t\27\4\30\t\30\3\2"+
		"\3\2\3\3\3\3\3\3\3\4\3\4\3\4\3\4\3\4\3\4\3\4\3\4\3\5\3\5\3\6\3\6\3\6\3"+
		"\6\3\6\3\6\3\6\3\7\3\7\3\7\3\7\3\7\3\7\3\7\3\b\3\b\3\t\3\t\3\t\3\t\3\t"+
		"\3\t\3\t\3\t\3\t\3\t\3\n\3\n\3\13\3\13\3\f\3\f\3\r\3\r\3\16\3\16\3\17"+
		"\3\17\3\20\3\20\3\21\3\21\3\22\3\22\3\23\3\23\3\23\3\23\3\23\3\24\3\24"+
		"\3\24\3\24\3\25\6\25w\n\25\r\25\16\25x\3\25\7\25|\n\25\f\25\16\25\177"+
		"\13\25\3\26\6\26\u0082\n\26\r\26\16\26\u0083\3\26\3\26\3\27\3\27\3\27"+
		"\3\27\7\27\u008c\n\27\f\27\16\27\u008f\13\27\3\27\3\27\3\27\3\27\3\27"+
		"\3\30\3\30\3\30\3\30\7\30\u009a\n\30\f\30\16\30\u009d\13\30\3\30\3\30"+
		"\3\u008d\2\31\3\3\5\4\7\5\t\6\13\7\r\b\17\t\21\n\23\13\25\f\27\r\31\16"+
		"\33\17\35\20\37\21!\22#\23%\24\'\25)\26+\27-\30/\31\3\2\6\6\2&&C\\aac"+
		"|\7\2&&\62;C\\aac|\5\2\13\f\17\17\"\"\4\2\f\f\17\17\2\u00a4\2\3\3\2\2"+
		"\2\2\5\3\2\2\2\2\7\3\2\2\2\2\t\3\2\2\2\2\13\3\2\2\2\2\r\3\2\2\2\2\17\3"+
		"\2\2\2\2\21\3\2\2\2\2\23\3\2\2\2\2\25\3\2\2\2\2\27\3\2\2\2\2\31\3\2\2"+
		"\2\2\33\3\2\2\2\2\35\3\2\2\2\2\37\3\2\2\2\2!\3\2\2\2\2#\3\2\2\2\2%\3\2"+
		"\2\2\2\'\3\2\2\2\2)\3\2\2\2\2+\3\2\2\2\2-\3\2\2\2\2/\3\2\2\2\3\61\3\2"+
		"\2\2\5\63\3\2\2\2\7\66\3\2\2\2\t>\3\2\2\2\13@\3\2\2\2\rG\3\2\2\2\17N\3"+
		"\2\2\2\21P\3\2\2\2\23Z\3\2\2\2\25\\\3\2\2\2\27^\3\2\2\2\31`\3\2\2\2\33"+
		"b\3\2\2\2\35d\3\2\2\2\37f\3\2\2\2!h\3\2\2\2#j\3\2\2\2%l\3\2\2\2\'q\3\2"+
		"\2\2)v\3\2\2\2+\u0081\3\2\2\2-\u0087\3\2\2\2/\u0095\3\2\2\2\61\62\7\60"+
		"\2\2\62\4\3\2\2\2\63\64\7]\2\2\64\65\7_\2\2\65\6\3\2\2\2\66\67\7r\2\2"+
		"\678\7c\2\289\7e\2\29:\7m\2\2:;\7c\2\2;<\7i\2\2<=\7g\2\2=\b\3\2\2\2>?"+
		"\7=\2\2?\n\3\2\2\2@A\7k\2\2AB\7o\2\2BC\7r\2\2CD\7q\2\2DE\7t\2\2EF\7v\2"+
		"\2F\f\3\2\2\2GH\7u\2\2HI\7v\2\2IJ\7c\2\2JK\7v\2\2KL\7k\2\2LM\7e\2\2M\16"+
		"\3\2\2\2NO\7,\2\2O\20\3\2\2\2PQ\7v\2\2QR\7{\2\2RS\7r\2\2ST\7g\2\2TU\7"+
		"u\2\2UV\7v\2\2VW\7c\2\2WX\7v\2\2XY\7g\2\2Y\22\3\2\2\2Z[\7}\2\2[\24\3\2"+
		"\2\2\\]\7\177\2\2]\26\3\2\2\2^_\7?\2\2_\30\3\2\2\2`a\7.\2\2a\32\3\2\2"+
		"\2bc\7<\2\2c\34\3\2\2\2de\7*\2\2e\36\3\2\2\2fg\7+\2\2g \3\2\2\2hi\7>\2"+
		"\2i\"\3\2\2\2jk\7@\2\2k$\3\2\2\2lm\7f\2\2mn\7t\2\2no\7q\2\2op\7r\2\2p"+
		"&\3\2\2\2qr\7g\2\2rs\7p\2\2st\7f\2\2t(\3\2\2\2uw\t\2\2\2vu\3\2\2\2wx\3"+
		"\2\2\2xv\3\2\2\2xy\3\2\2\2y}\3\2\2\2z|\t\3\2\2{z\3\2\2\2|\177\3\2\2\2"+
		"}{\3\2\2\2}~\3\2\2\2~*\3\2\2\2\177}\3\2\2\2\u0080\u0082\t\4\2\2\u0081"+
		"\u0080\3\2\2\2\u0082\u0083\3\2\2\2\u0083\u0081\3\2\2\2\u0083\u0084\3\2"+
		"\2\2\u0084\u0085\3\2\2\2\u0085\u0086\b\26\2\2\u0086,\3\2\2\2\u0087\u0088"+
		"\7\61\2\2\u0088\u0089\7,\2\2\u0089\u008d\3\2\2\2\u008a\u008c\13\2\2\2"+
		"\u008b\u008a\3\2\2\2\u008c\u008f\3\2\2\2\u008d\u008e\3\2\2\2\u008d\u008b"+
		"\3\2\2\2\u008e\u0090\3\2\2\2\u008f\u008d\3\2\2\2\u0090\u0091\7,\2\2\u0091"+
		"\u0092\7\61\2\2\u0092\u0093\3\2\2\2\u0093\u0094\b\27\2\2\u0094.\3\2\2"+
		"\2\u0095\u0096\7\61\2\2\u0096\u0097\7\61\2\2\u0097\u009b\3\2\2\2\u0098"+
		"\u009a\n\5\2\2\u0099\u0098\3\2\2\2\u009a\u009d\3\2\2\2\u009b\u0099\3\2"+
		"\2\2\u009b\u009c\3\2\2\2\u009c\u009e\3\2\2\2\u009d\u009b\3\2\2\2\u009e"+
		"\u009f\b\30\2\2\u009f\60\3\2\2\2\b\2x}\u0083\u008d\u009b\3\b\2\2";
	public static final ATN _ATN =
		new ATNDeserializer().deserialize(_serializedATN.toCharArray());
	static {
		_decisionToDFA = new DFA[_ATN.getNumberOfDecisions()];
		for (int i = 0; i < _ATN.getNumberOfDecisions(); i++) {
			_decisionToDFA[i] = new DFA(_ATN.getDecisionState(i), i);
		}
	}
}