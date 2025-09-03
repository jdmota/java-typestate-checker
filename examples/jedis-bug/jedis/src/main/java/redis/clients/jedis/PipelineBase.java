package redis.clients.jedis;

import java.util.List;
import java.util.Map;
import java.util.Set;

import redis.clients.jedis.commands.BinaryRedisPipeline;
import redis.clients.jedis.commands.RedisPipeline;


public abstract class PipelineBase extends Queable implements BinaryRedisPipeline, RedisPipeline {

  protected abstract Client getClient(String key);

  protected abstract Client getClient(byte[] key);

  @Override
  public Response<Set<String>> zrevrange(final String key, final long start, final long stop) {
    getClient(key).zrevrange(key, start, stop);
    return getResponse(BuilderFactory.STRING_ZSET);
  }

  @Override
  public Response<Set<byte[]>> zrevrange(final byte[] key, final long start, final long stop) {
    getClient(key).zrevrange(key, start, stop);
    return getResponse(BuilderFactory.BYTE_ARRAY_ZSET);
  }
}
