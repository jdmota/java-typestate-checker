package demos.loop;

/**
 * Arguably the loop typestate itself is inhabited (since we can create an object that
 * implements it), but its (informal) dual is uninhabited, in that we cannot define a
 * client that consumes the loop.
 */

@Typestate("Loop")
class LoopImpl{
  	Bool finished() {
  		return Bool.TRUE;
  	}
}
