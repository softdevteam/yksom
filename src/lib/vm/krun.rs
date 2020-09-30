use libc::{c_double, c_int};

extern "C" {
    pub(crate) fn krun_init();

    pub(crate) fn krun_done();

    pub(crate) fn krun_measure(mdata_idx: c_int);

    pub(crate) fn krun_get_core_cycles_double(mdata_idx: c_int, core: c_int) -> c_double;

    pub(crate) fn krun_get_num_cores() -> c_int;

    pub(crate) fn krun_get_wallclock(mdata_idx: c_int) -> c_double;
}
