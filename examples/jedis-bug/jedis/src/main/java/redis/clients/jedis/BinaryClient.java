package redis.clients.jedis;

import static redis.clients.jedis.Protocol.toByteArray;
import static redis.clients.jedis.Protocol.Command.*;
import static redis.clients.jedis.Protocol.Keyword.ENCODING;
import static redis.clients.jedis.Protocol.Keyword.IDLETIME;
import static redis.clients.jedis.Protocol.Keyword.LEN;
import static redis.clients.jedis.Protocol.Keyword.LIMIT;
import static redis.clients.jedis.Protocol.Keyword.NO;
import static redis.clients.jedis.Protocol.Keyword.ONE;
import static redis.clients.jedis.Protocol.Keyword.REFCOUNT;
import static redis.clients.jedis.Protocol.Keyword.RESET;
import static redis.clients.jedis.Protocol.Keyword.STORE;
import static redis.clients.jedis.Protocol.Keyword.WITHSCORES;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import javax.net.ssl.HostnameVerifier;
import javax.net.ssl.SSLParameters;
import javax.net.ssl.SSLSocketFactory;

import redis.clients.jedis.Protocol.Keyword;
import redis.clients.jedis.util.SafeEncoder;

public class BinaryClient extends Connection {

  private boolean isInMulti;

  private String password;

  private int db;

  private boolean isInWatch;

  public BinaryClient() {
    super();
  }

  public BinaryClient(final String host) {
    super(host);
  }

  public BinaryClient(final String host, final int port) {
    super(host, port);
  }

  public BinaryClient(final String host, final int port, final boolean ssl) {
    super(host, port, ssl);
  }

  public BinaryClient(final String host, final int port, final boolean ssl,
      final SSLSocketFactory sslSocketFactory, final SSLParameters sslParameters,
      final HostnameVerifier hostnameVerifier) {
    super(host, port, ssl, sslSocketFactory, sslParameters, hostnameVerifier);
  }

  public void zrevrange(final byte[] key, final long start, final long stop) {
    sendCommand(ZREVRANGE, key, toByteArray(start), toByteArray(stop));
  }

  public void discard() {
    sendCommand(DISCARD);
    isInMulti = false;
    isInWatch = false;
  }


}
