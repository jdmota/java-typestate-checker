package redis.clients.jedis.commands;

import java.util.List;

import redis.clients.jedis.params.MigrateParams;
import redis.clients.jedis.params.ClientKillParams;
import redis.clients.jedis.util.Slowlog;

public interface AdvancedJedisCommands {
  List<String> configGet(String pattern);

  String configSet(String parameter, String value);

  String slowlogReset();

  Long slowlogLen();

  List<Slowlog> slowlogGet();

  List<Slowlog> slowlogGet(long entries);

  Long objectRefcount(String key);

  String objectEncoding(String key);

  Long objectIdletime(String key);

  String migrate(String host, int port, String key, int destinationDB, int timeout);

  String migrate(String host, int port, int destinationDB, int timeout, MigrateParams params, String... keys);

  String clientKill(String ipPort);

  String clientKill(String ip, int port);

  Long clientKill(ClientKillParams params);

  String clientGetname();

  String clientList();

  String clientSetname(String name);

  String memoryDoctor();
}
