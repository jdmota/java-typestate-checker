import java.io.FileReader;
import java.io.IOException;
import java.lang.Thread;
import mungo.lib.Typestate;
import jatyc.lib.Nullable;

@Typestate("LineReader.protocol")
public class LineReader {
  private @Nullable FileReader file;
  private int curr;

  public LineReader() {
    this.file = null;
    this.curr = 0;
  }

  public Status open(String filename) {
    try {
      file = new FileReader(filename);
      curr = file.read();
      return Status.OK;
    } catch (IOException exp) {
      return Status.ERROR;
    }
  }

  public String read() throws IOException {
    StringBuilder str = new StringBuilder();

    while (curr != 10 && curr != -1) {
      str.append((char) curr);
      curr = file.read();
    }

    if (curr == 10) {
      curr = file.read();
    }

    return str.toString();
  }

  public boolean eof() {
    return curr == -1;
  }

  public void close() throws IOException {
    file.close();
  }
}
