import Noctium.Frontend

open scoped Noctium

noctium_circuit pauseInputs where
  public active : Bool
end

noctium_contract GuardedPauseEvents where
  entry logGuardedPause uses pauseInputs where
    when active emitEvent(Paused)
    when active emitEvent(Unpaused)
  end
end

/-- error: unknown field 'reason' for event 'Paused' -/
#guard_msgs in
noctium_contract InvalidPausedEvent where
  entry invalid uses pauseInputs where
    emitEvent(Paused, reason := active)
  end
end

/-- error: unknown field 'reason' for event 'Unpaused' -/
#guard_msgs in
noctium_contract InvalidUnpausedEvent where
  entry invalid uses pauseInputs where
    emitEvent(Unpaused, reason := active)
  end
end
