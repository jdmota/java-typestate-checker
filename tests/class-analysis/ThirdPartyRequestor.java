import jatyc.lib.Typestate;

@Typestate("ThirdPartyRequestor")
public class ThirdPartyRequestor {

  public void await() {

  }

  public SharingState requestAccess() {
    // :: warning: (SharingState.PENDING: Shared{SharingState})
    return SharingState.PENDING;
  }

  public OwnerResponse awaitResponse() {
    // :: error: (Incompatible return value: cannot cast from Null to Shared{OwnerResponse})
    return null;
  }

  public SharingState revokedByOwner() {
    // :: error: (Incompatible return value: cannot cast from Null to Shared{SharingState})
    return null;
  }

  public void releaseAccess() {

  }
}
