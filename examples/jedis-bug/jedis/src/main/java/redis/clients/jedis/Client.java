package redis.clients.jedis;

import static redis.clients.jedis.Protocol.toByteArray;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import javax.net.ssl.HostnameVerifier;
import javax.net.ssl.SSLParameters;
import javax.net.ssl.SSLSocketFactory;

import redis.clients.jedis.commands.Commands;
import redis.clients.jedis.util.SafeEncoder;

public class Client extends BinaryClient implements Commands {

  public Client() {
    super();
  }

  public Client(final String host) {
    super(host);
  }

  public Client(final String host, final int port) {
    super(host, port);
  }

  public Client(final String host, final int port, final boolean ssl) {
    super(host, port, ssl);
  }

  public Client(final String host, final int port, final boolean ssl,
      final SSLSocketFactory sslSocketFactory, final SSLParameters sslParameters,
      final HostnameVerifier hostnameVerifier) {
    super(host, port, ssl, sslSocketFactory, sslParameters, hostnameVerifier);
  }

  @Override
  public void zrevrange(final String key, final long start, final long stop) {
    zrevrange(SafeEncoder.encode(key), start, stop);
  }

}
