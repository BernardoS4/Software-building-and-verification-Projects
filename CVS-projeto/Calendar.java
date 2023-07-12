import java.util.Date;

public interface Calendar {
    /*@
    predicate CalendarInv(boolean rw);
    @*/
    Appointment addAppointment(String description, Date date, int minutes, User[] attendees);
    //@ requires CalendarInv(true) &*& description != null &*& date != null &*& attendees != null;
    //@ ensures CalendarInv(true) &*& result != null;
    void removeAppointment(Appointment a);
    //@ requires CalendarInv(true) &*& a != null &*& a.isValid();
    //@ ensures CalendarInv(true);
    boolean isFree(Date date, int minutes);
    //@ requires CalendarInv(_) &*& date != null;
    //@ ensures CalendarInv(_);
    Appointment[] listAppointments(Date startDate, Date endDate);
    //@ requires CalendarInv(_) &*& startDate != null &*& endDate != null &*& lessOrEqual(startDate,endDate)
    //@ ensures CalendarInv(_);
    void LockCalendar();
    //@ requires CalendarInv(true);
    //@ ensures CalendarInv(false);
    void UnlockCalendar();
    //@ requires CalendarInv(false);
    //@ ensures CalendarInv(true);
    boolean isReadOnly();
    //@ requires CalendarInv(?rw);
    //@ ensures CalendarInv(rw) &*& result == rw;
    }

