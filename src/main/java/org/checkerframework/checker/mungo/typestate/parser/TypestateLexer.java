// Generated from org\checkerframework\checker\mungo\typestate\parser\Typestate.g4 by ANTLR 4.8

package org.checkerframework.checker.mungo.typestate.parser;
import org.checkerframework.checker.mungo.typestate.ast.*;
import static org.checkerframework.checker.mungo.typestate.ast.Position.tokenToPos;
import static org.checkerframework.checker.mungo.typestate.Utils.map;

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
		T__9=10, T__10=11, T__11=12, T__12=13, T__13=14, T__14=15, ID=16, WS=17, 
		BlockComment=18, LineComment=19;
	public static String[] channelNames = {
		"DEFAULT_TOKEN_CHANNEL", "HIDDEN"
	};

	public static String[] modeNames = {
		"DEFAULT_MODE"
	};

	private static String[] makeRuleNames() {
		return new String[] {
			"T__0", "T__1", "T__2", "T__3", "T__4", "T__5", "T__6", "T__7", "T__8", 
			"T__9", "T__10", "T__11", "T__12", "T__13", "T__14", "ID", "WS", "BlockComment", 
			"LineComment"
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
		"\3\u608b\ua72a\u8133\ub9ed\u417c\u3be7\u7786\u5964\2\25\u0085\b\1\4\2"+
		"\t\2\4\3\t\3\4\4\t\4\4\5\t\5\4\6\t\6\4\7\t\7\4\b\t\b\4\t\t\t\4\n\t\n\4"+
		"\13\t\13\4\f\t\f\4\r\t\r\4\16\t\16\4\17\t\17\4\20\t\20\4\21\t\21\4\22"+
		"\t\22\4\23\t\23\4\24\t\24\3\2\3\2\3\2\3\2\3\2\3\2\3\2\3\2\3\3\3\3\3\4"+
		"\3\4\3\5\3\5\3\5\3\5\3\5\3\5\3\5\3\6\3\6\3\7\3\7\3\7\3\7\3\7\3\7\3\7\3"+
		"\7\3\7\3\7\3\b\3\b\3\t\3\t\3\n\3\n\3\13\3\13\3\f\3\f\3\r\3\r\3\16\3\16"+
		"\3\17\3\17\3\20\3\20\3\21\6\21\\\n\21\r\21\16\21]\3\21\7\21a\n\21\f\21"+
		"\16\21d\13\21\3\22\6\22g\n\22\r\22\16\22h\3\22\3\22\3\23\3\23\3\23\3\23"+
		"\7\23q\n\23\f\23\16\23t\13\23\3\23\3\23\3\23\3\23\3\23\3\24\3\24\3\24"+
		"\3\24\7\24\177\n\24\f\24\16\24\u0082\13\24\3\24\3\24\3r\2\25\3\3\5\4\7"+
		"\5\t\6\13\7\r\b\17\t\21\n\23\13\25\f\27\r\31\16\33\17\35\20\37\21!\22"+
		"#\23%\24\'\25\3\2\6\6\2&&C\\aac|\7\2&&\62;C\\aac|\5\2\13\f\17\17\"\"\4"+
		"\2\f\f\17\17\2\u0089\2\3\3\2\2\2\2\5\3\2\2\2\2\7\3\2\2\2\2\t\3\2\2\2\2"+
		"\13\3\2\2\2\2\r\3\2\2\2\2\17\3\2\2\2\2\21\3\2\2\2\2\23\3\2\2\2\2\25\3"+
		"\2\2\2\2\27\3\2\2\2\2\31\3\2\2\2\2\33\3\2\2\2\2\35\3\2\2\2\2\37\3\2\2"+
		"\2\2!\3\2\2\2\2#\3\2\2\2\2%\3\2\2\2\2\'\3\2\2\2\3)\3\2\2\2\5\61\3\2\2"+
		"\2\7\63\3\2\2\2\t\65\3\2\2\2\13<\3\2\2\2\r>\3\2\2\2\17H\3\2\2\2\21J\3"+
		"\2\2\2\23L\3\2\2\2\25N\3\2\2\2\27P\3\2\2\2\31R\3\2\2\2\33T\3\2\2\2\35"+
		"V\3\2\2\2\37X\3\2\2\2![\3\2\2\2#f\3\2\2\2%l\3\2\2\2\'z\3\2\2\2)*\7r\2"+
		"\2*+\7c\2\2+,\7e\2\2,-\7m\2\2-.\7c\2\2./\7i\2\2/\60\7g\2\2\60\4\3\2\2"+
		"\2\61\62\7\60\2\2\62\6\3\2\2\2\63\64\7=\2\2\64\b\3\2\2\2\65\66\7k\2\2"+
		"\66\67\7o\2\2\678\7r\2\289\7q\2\29:\7t\2\2:;\7v\2\2;\n\3\2\2\2<=\7,\2"+
		"\2=\f\3\2\2\2>?\7v\2\2?@\7{\2\2@A\7r\2\2AB\7g\2\2BC\7u\2\2CD\7v\2\2DE"+
		"\7c\2\2EF\7v\2\2FG\7g\2\2G\16\3\2\2\2HI\7}\2\2I\20\3\2\2\2JK\7\177\2\2"+
		"K\22\3\2\2\2LM\7?\2\2M\24\3\2\2\2NO\7.\2\2O\26\3\2\2\2PQ\7*\2\2Q\30\3"+
		"\2\2\2RS\7+\2\2S\32\3\2\2\2TU\7<\2\2U\34\3\2\2\2VW\7>\2\2W\36\3\2\2\2"+
		"XY\7@\2\2Y \3\2\2\2Z\\\t\2\2\2[Z\3\2\2\2\\]\3\2\2\2][\3\2\2\2]^\3\2\2"+
		"\2^b\3\2\2\2_a\t\3\2\2`_\3\2\2\2ad\3\2\2\2b`\3\2\2\2bc\3\2\2\2c\"\3\2"+
		"\2\2db\3\2\2\2eg\t\4\2\2fe\3\2\2\2gh\3\2\2\2hf\3\2\2\2hi\3\2\2\2ij\3\2"+
		"\2\2jk\b\22\2\2k$\3\2\2\2lm\7\61\2\2mn\7,\2\2nr\3\2\2\2oq\13\2\2\2po\3"+
		"\2\2\2qt\3\2\2\2rs\3\2\2\2rp\3\2\2\2su\3\2\2\2tr\3\2\2\2uv\7,\2\2vw\7"+
		"\61\2\2wx\3\2\2\2xy\b\23\2\2y&\3\2\2\2z{\7\61\2\2{|\7\61\2\2|\u0080\3"+
		"\2\2\2}\177\n\5\2\2~}\3\2\2\2\177\u0082\3\2\2\2\u0080~\3\2\2\2\u0080\u0081"+
		"\3\2\2\2\u0081\u0083\3\2\2\2\u0082\u0080\3\2\2\2\u0083\u0084\b\24\2\2"+
		"\u0084(\3\2\2\2\b\2]bhr\u0080\3\b\2\2";
	public static final ATN _ATN =
		new ATNDeserializer().deserialize(_serializedATN.toCharArray());
	static {
		_decisionToDFA = new DFA[_ATN.getNumberOfDecisions()];
		for (int i = 0; i < _ATN.getNumberOfDecisions(); i++) {
			_decisionToDFA[i] = new DFA(_ATN.getDecisionState(i), i);
		}
	}
}