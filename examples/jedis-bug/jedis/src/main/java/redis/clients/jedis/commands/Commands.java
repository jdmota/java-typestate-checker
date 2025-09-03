package redis.clients.jedis.commands;



public interface Commands {
  void zrevrange(String key, long start, long stop);
}
