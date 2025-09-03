package redis.clients.jedis.commands;

import redis.clients.jedis.Response;

import java.util.List;
import java.util.Map;
import java.util.Set;

public interface BinaryRedisPipeline {
  Response<Set<byte[]>> zrevrange(byte[] key, long start, long stop);
}
