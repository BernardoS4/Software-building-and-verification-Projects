import java.util.Date;
import java.util.concurrent.locks.Condition;
import java.util.concurrent.locks.ReentrantLock;

/*@
    predicate_ctor CCalendar_shared_state(CCalendar cc)() =
    cc.calendar |-> ?c &*&
    c != null &*&
    c.CalendarInv(_);

    predicate_ctor CCalendar_okToWrite_state(cc)() =
     cc.calendar |-> ?c &*&
    c != null &*&
    c.CalendarInv(true);

    predicate CalendarInv(CCalendar cc;) = 
    cc.mon |-> ?m &*&
    m != null &*&
    lck(m, 1, CCalendar_shared_state(cc)) &*&
    cc.okToWrite |-> ?otw &*&
    otw != null &*&
    cnd(otw, CCalendar_shared_state(cc)), CCalendar_okToWrite_state(cc));
@*/

public class CCalendar implements Calendar{

    Calendar calendar;
    ReentrantLock mon;
    Condition okToWrite;

    public CCalendar()
    //@ requires true;
    //@ ensures CalendarInv(this);
    {
        calendar = new Calendar();
        //@ close CCalendar_shared_state(this)();
        //@ close enter_lck(1, CCalendar_shared_state(this));
        mon = new ReentrantLock();
        //@ close set_cond(CCalendar_shared_state(this), CCalendar_okToWrite_state(this));
        okToWrite = mon.newCondition();
        //@ close CalendarInv(this);
    }


    @Override
    public Appointment addAppointment(String description, Date date, int minutes, User[] attendees) 
    //@ requires CalendarInv(this);
    //@ ensures CalendarInv(true);
    {
        mon.lock();
        //@ open CCalendar_shared_state(this)();

        if(isFree(date, minutes)){
            Appointment a = calendar.addAppointment(description, date, minutes, attendees);
        }

        return a;
    }

    @Override
    public void removeAppointment(Appointment a) 
    //@ requires CalendarInv(true) &*& a != null &*& a.isValid();
    //@ ensures CalendarInv(true);
    {
        throw new UnsupportedOperationException("Unimplemented method 'removeAppointment'");
    }

    @Override
    public boolean isFree(Date date, int minutes) 
    //@ requires CalendarInv(_) &*& date != null;
    //@ ensures CalendarInv(_);
    {
        throw new UnsupportedOperationException("Unimplemented method 'isFree'");
    }

    @Override
    public Appointment[] listAppointments(Date startDate, Date endDate) 
    //@ requires CalendarInv(_) &*& startDate != null &*& endDate != null &*& lessOrEqual(startDate,endDate)
    //@ ensures CalendarInv(_);
    {
        throw new UnsupportedOperationException("Unimplemented method 'listAppointments'");
    }

    @Override
    public void LockCalendar() 
    //@ requires CalendarInv(true);
    //@ ensures CalendarInv(false);
    {
        throw new UnsupportedOperationException("Unimplemented method 'LockCalendar'");
    }

    @Override
    public void UnlockCalendar() 
    //@ requires CalendarInv(false);
    //@ ensures CalendarInv(true);
    {
        throw new UnsupportedOperationException("Unimplemented method 'UnlockCalendar'");
    }

    @Override
    public boolean isReadOnly() 
    //@ requires CalendarInv(?rw);
    //@ ensures CalendarInv(rw) &*& result == rw;
    {
        throw new UnsupportedOperationException("Unimplemented method 'isReadOnly'");
    }
    
}
