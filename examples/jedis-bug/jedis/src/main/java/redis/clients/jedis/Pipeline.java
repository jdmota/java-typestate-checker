package redis.clients.jedis;

import java.io.Closeable;
import java.util.ArrayList;
import java.util.List;

import redis.clients.jedis.exceptions.JedisDataException;

public class Pipeline extends MultiKeyPipelineBase implements Closeable {
  public void setClient(Client client) {
    this.client = client;
  }

  @Override
  protected Client getClient(byte[] key) {
    return client;
  }

  @Override
  protected Client getClient(String key) {
    return client;
  }

  /**
   * Synchronize pipeline by reading all responses. This operation close the pipeline. In order to
   * get return values from pipelined commands, capture the different Response&lt;?&gt; of the
   * commands you execute.
   */
  public void sync() {
    if (getPipelinedResponseLength() > 0) {
      List<Object> unformatted = client.getMany(getPipelinedResponseLength());
      for (Object o : unformatted) {
        generateResponse(o);
      }
    }
  }
  public void close() {}
}
