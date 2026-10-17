/*
 * ================================================================
 *            DEADLOCK DETECTION AND RECOVERY SIMULATOR
 * ================================================================
 *
 * Compile:
 *   gcc -std=c11 -Wall -Wextra -Wpedantic -O2 deadlock_simulator.c -o deadlock_simulator
 *
 * Run:
 *   ./deadlock_simulator
 *
 * Platform: Linux / Ubuntu / WSL (pure standard C, no external libs)
 *
 * ----------------------------------------------------------------
 * DATA MODEL
 * ----------------------------------------------------------------
 *   Total[j]         instances of resource type j that exist
 *   Allocation[i][j] instances of resource j currently HELD by process i
 *   Request[i][j]    ADDITIONAL instances of resource j process i waits for
 *   Available[j]     Total[j] - sum over i of Allocation[i][j]
 *
 * ----------------------------------------------------------------
 * ALGORITHMS (summary - see README.md for the long version)
 * ----------------------------------------------------------------
 * Detection (Work / Finish method, multiple instances):
 *   Work   = Available
 *   Finish[i] = true  if process i is terminated or holds nothing
 *             = false otherwise
 *   repeat: find i with Finish[i]==false and Request[i] <= Work
 *           (every resource type);  Work += Allocation[i];
 *           Finish[i] = true; append i to completion sequence
 *   until no such i exists.
 *   Every i with Finish[i]==false is DEADLOCKED.
 *   Detection works on local copies; it never changes the system.
 *
 * Recovery (process termination, purely simulated):
 *   Strategy A - terminate ONE chosen deadlocked process
 *   Strategy B - terminate ALL currently deadlocked processes
 *   Termination releases the victim's Allocation, deletes its
 *   Request row, marks it TERMINATED and recomputes Available.
 *   Detection is then run AGAIN to verify the real outcome.
 *   No real Linux process is ever touched.
 *
 * ----------------------------------------------------------------
 * TEST PLAN (full expected values are in README.md)
 * ----------------------------------------------------------------
 *   T1  Deadlock-free system, every process can finish
 *   T2  Two processes / two resource types circular wait
 *   T3  Deadlock among three or more processes
 *   T4  Multiple instances per resource type
 *   T5  Zero available resources
 *   T6  Some processes hold nothing
 *   T7  Recovery: terminate one selected process
 *   T8  Recovery: terminate all deadlocked processes
 *   T9  Terminating one process does NOT fix every deadlock
 *   T10 Invalid input: letters, negatives, over-allocation
 *   T11 Reset, then enter brand-new data
 *   T12 Detection run repeatedly - state must not change
 * ================================================================
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <ctype.h>
#include <errno.h>

/* ================================================================
   CONSTANTS AND DATA STRUCTURES
   ================================================================ */

#define MAX_PROCESSES   20
#define MAX_RESOURCES   20
#define MAX_INSTANCES   1000
#define NAME_LEN        16
#define INPUT_BUFFER    512

/* Result codes of validate_input() */
#define INPUT_OK            0
#define INPUT_EMPTY         1
#define INPUT_NOT_INTEGER   2
#define INPUT_OUT_OF_RANGE  3

/* Output of one run of the detection algorithm */
typedef struct
{
    int valid;                          /* 1 once detection has been run   */
    int deadlock_found;                 /* 1 if at least one process stuck */
    int sequence[MAX_PROCESSES];        /* completion sequence             */
    int sequence_length;
    int deadlocked[MAX_PROCESSES];      /* deadlocked process indices      */
    int deadlocked_count;
    int idle[MAX_PROCESSES];            /* active processes holding nothing*/
    int idle_count;
    int work_final[MAX_RESOURCES];      /* resources free after all that   */
                                        /* could finish have finished      */
} DetectionResult;

/* Complete simulation state */
typedef struct
{
    int  configured;                    /* option 1 completed              */
    int  data_entered;                  /* option 2 completed              */

    int  num_processes;
    int  num_resources;

    char process_name[MAX_PROCESSES][NAME_LEN];
    char resource_name[MAX_RESOURCES][NAME_LEN];

    int  total[MAX_RESOURCES];
    int  available[MAX_RESOURCES];
    int  allocation[MAX_PROCESSES][MAX_RESOURCES];
    int  request[MAX_PROCESSES][MAX_RESOURCES];
    int  terminated[MAX_PROCESSES];     /* 1 = terminated by recovery      */

    DetectionResult last_detection;

    int  history_pid[MAX_PROCESSES];    /* recovery history                */
    char history_strategy[MAX_PROCESSES];
    int  history_count;
} SystemState;

static SystemState simulation;          /* the one simulation instance     */
static int input_eof = 0;               /* set when stdin reaches EOF      */

/* ================================================================
   FUNCTION DECLARATIONS
   ================================================================ */

/* Utility / presentation */
static void print_line(void);
static void print_header(const char *title);
static void print_banner(void);
static void display_main_menu(void);

/* Input handling */
static int  read_line(char *buffer, size_t size);
static int  validate_input(const char *text, long min, long max, long *value);
static int  read_int_in_range(const char *prompt, long min, long max, long *value);
static int  ask_yes_no(const char *prompt);
static int  parse_row(const char *line, int count, const int *max_values,
                      const SystemState *s, int *out_values);

/* State management */
static void reset_simulation(SystemState *s);
static void clear_matrix_data(SystemState *s);
static int  require_configured(const SystemState *s);
static int  require_ready(const SystemState *s);

/* Configuration and data entry */
static void configure_system(SystemState *s);
static int  enter_allocation_data(SystemState *s);
static int  enter_request_data(SystemState *s);
static void enter_data_menu(SystemState *s);
static int  calculate_available_resources(SystemState *s);
static int  validate_configuration(const SystemState *s);

/* Display */
static void print_vector(const int *values, int count);
static void print_process_list(const SystemState *s, const int *ids, int count);
static void print_matrix(const SystemState *s, const char *title, int use_request);
static void display_system_state(const SystemState *s);
static void display_detection_result(const SystemState *s, const DetectionResult *r);

/* Detection and recovery */
static void detect_deadlock(const SystemState *s, DetectionResult *result);
static int  terminate_process(SystemState *s, int pid, char strategy, int *released);
static int  recover_by_terminating_process(SystemState *s, int pid);
static int  recover_by_terminating_all_deadlocked(SystemState *s);
static int  select_deadlocked_process(const SystemState *s);
static void recovery_session(SystemState *s);

/* Menu actions */
static void menu_detect_deadlock(SystemState *s);
static void menu_recover(SystemState *s);
static void print_final_summary(const SystemState *s);
static void run_complete_simulation(SystemState *s);

/* ================================================================
   UTILITY AND PRESENTATION FUNCTIONS
   ================================================================ */

static void print_line(void)
{
    printf("------------------------------------------------------------\n");
}

static void print_header(const char *title)
{
    printf("\n============================================================\n");
    printf(" %s\n", title);
    printf("============================================================\n");
}

static void print_banner(void)
{
    printf("\n");
    printf("################################################################\n");
    printf("#                                                              #\n");
    printf("#            DEADLOCK DETECTION AND RECOVERY SIMULATOR         #\n");
    printf("#                                                              #\n");
    printf("#                  OPERATING SYSTEM PROJECT                    #\n");
    printf("#                                                              #\n");
    printf("################################################################\n");
}

static void display_main_menu(void)
{
    print_header("MAIN MENU");

    printf("1. Configure Processes and Resources\n");
    printf("2. Enter Resource Allocation and Request Data\n");
    printf("3. Display Current System State\n");
    printf("4. Detect Deadlock\n");
    printf("5. Recover from Deadlock\n");
    printf("6. Run Complete Simulation\n");
    printf("7. Reset Simulation\n");
    printf("0. Exit\n");
}

/* ================================================================
   INPUT HANDLING
   ================================================================ */

/*
 * Reads one line with fgets(). Strips the newline / carriage return.
 * Over-long lines are discarded and replaced by "?" so that they fail
 * validation instead of leaking into the next prompt.
 * Returns 1 on success, 0 on end-of-file.
 */
static int read_line(char *buffer, size_t size)
{
    if (input_eof)
        return 0;

    if (fgets(buffer, (int)size, stdin) == NULL)
    {
        input_eof = 1;
        buffer[0] = '\0';
        return 0;
    }

    size_t len = strlen(buffer);

    if (len > 0 && buffer[len - 1] == '\n')
    {
        buffer[--len] = '\0';
        if (len > 0 && buffer[len - 1] == '\r')
            buffer[--len] = '\0';
    }
    else if (!feof(stdin))
    {
        /* line did not fit in the buffer: throw away the rest */
        int c;
        while ((c = getchar()) != '\n' && c != EOF)
            ;
        strcpy(buffer, "?");
    }

    return 1;
}

/*
 * validate_input: strictly parses a whole string as one integer and
 * checks min <= value <= max. Rejects letters, trailing garbage,
 * empty text and overflow. Nothing is written to *value on failure.
 */
static int validate_input(const char *text, long min, long max, long *value)
{
    const char *p = text;

    while (*p != '\0' && isspace((unsigned char)*p))
        p++;

    if (*p == '\0')
        return INPUT_EMPTY;

    char *end = NULL;
    errno = 0;
    long parsed = strtol(p, &end, 10);

    if (end == p)
        return INPUT_NOT_INTEGER;

    if (errno == ERANGE)
        return INPUT_OUT_OF_RANGE;

    while (*end != '\0' && isspace((unsigned char)*end))
        end++;

    if (*end != '\0')
        return INPUT_NOT_INTEGER;

    if (parsed < min || parsed > max)
        return INPUT_OUT_OF_RANGE;

    *value = parsed;
    return INPUT_OK;
}

/*
 * Prompts until the user types an integer in [min, max].
 * Returns 1 on success, 0 on EOF.
 */
static int read_int_in_range(const char *prompt, long min, long max, long *value)
{
    char line[INPUT_BUFFER];

    for (;;)
    {
        printf("%s", prompt);
        fflush(stdout);

        if (!read_line(line, sizeof(line)))
        {
            printf("\n[!] End of input reached.\n");
            return 0;
        }

        switch (validate_input(line, min, max, value))
        {
        case INPUT_OK:
            return 1;
        case INPUT_EMPTY:
            printf("[!] Nothing entered. Please type a number.\n");
            break;
        case INPUT_NOT_INTEGER:
            printf("[!] Invalid input. Please enter a whole number.\n");
            break;
        default:
            printf("[!] Value out of range. Allowed range: %ld to %ld.\n", min, max);
            break;
        }
    }
}

/* Asks a y/n question. Returns 1 for yes, 0 for no (or EOF). */
static int ask_yes_no(const char *prompt)
{
    char line[INPUT_BUFFER];

    for (;;)
    {
        printf("%s", prompt);
        fflush(stdout);

        if (!read_line(line, sizeof(line)))
        {
            printf("\n[!] End of input reached. Assuming 'no'.\n");
            return 0;
        }

        const char *p = line;
        while (*p != '\0' && isspace((unsigned char)*p))
            p++;

        if (tolower((unsigned char)p[0]) == 'y')
            return 1;
        if (tolower((unsigned char)p[0]) == 'n')
            return 0;

        printf("[!] Please answer y or n.\n");
    }
}

/*
 * Parses one matrix row: exactly 'count' whitespace-separated integers,
 * value k must be in [0, max_values[k]]. Prints a precise error and
 * returns 0 on failure; writes out_values only when the whole row is OK.
 */
static int parse_row(const char *line, int count, const int *max_values,
                     const SystemState *s, int *out_values)
{
    int  parsed[MAX_RESOURCES];
    const char *p = line;

    for (int k = 0; k < count; k++)
    {
        while (*p != '\0' && isspace((unsigned char)*p))
            p++;

        if (*p == '\0')
        {
            printf("[!] Expected %d values but only %d were entered.\n", count, k);
            return 0;
        }

        char token[32];
        size_t len = 0;
        int too_long = 0;

        while (*p != '\0' && !isspace((unsigned char)*p))
        {
            if (len < sizeof(token) - 1)
                token[len++] = *p;
            else
                too_long = 1;
            p++;
        }
        token[len] = '\0';

        long value = 0;
        int  code  = too_long ? INPUT_NOT_INTEGER
                              : validate_input(token, 0, max_values[k], &value);

        if (code == INPUT_NOT_INTEGER || code == INPUT_EMPTY)
        {
            printf("[!] '%s' is not a valid whole number (value %d, %s).\n",
                   token, k + 1, s->resource_name[k]);
            return 0;
        }
        if (code == INPUT_OUT_OF_RANGE)
        {
            if (max_values[k] == 0)
                printf("[!] No instances of %s are left for this entry; "
                       "the only valid value is 0.\n", s->resource_name[k]);
            else
                printf("[!] Value for %s must be between 0 and %d "
                       "(negative values and over-allocation are rejected).\n",
                       s->resource_name[k], max_values[k]);
            return 0;
        }

        parsed[k] = (int)value;
    }

    while (*p != '\0' && isspace((unsigned char)*p))
        p++;

    if (*p != '\0')
    {
        printf("[!] Too many values. Exactly %d values are required.\n", count);
        return 0;
    }

    for (int k = 0; k < count; k++)
        out_values[k] = parsed[k];

    return 1;
}

/* ================================================================
   STATE MANAGEMENT
   ================================================================ */

/* Clears allocation/request/termination/detection data (keeps config) */
static void clear_matrix_data(SystemState *s)
{
    memset(s->allocation, 0, sizeof(s->allocation));
    memset(s->request, 0, sizeof(s->request));
    memset(s->terminated, 0, sizeof(s->terminated));
    memset(&s->last_detection, 0, sizeof(s->last_detection));
    memset(s->history_pid, 0, sizeof(s->history_pid));
    memset(s->history_strategy, 0, sizeof(s->history_strategy));
    s->history_count = 0;
    s->data_entered = 0;

    for (int j = 0; j < MAX_RESOURCES; j++)
        s->available[j] = s->total[j];
}

/* Option 7: wipes everything so a completely new run can start */
static void reset_simulation(SystemState *s)
{
    memset(s, 0, sizeof(*s));
}

static int require_configured(const SystemState *s)
{
    if (!s->configured)
    {
        printf("\n[!] The system is not configured yet.\n");
        printf("    Use option 1 (Configure Processes and Resources) first.\n");
        return 0;
    }
    return 1;
}

/* Detection / recovery need configuration AND allocation/request data */
static int require_ready(const SystemState *s)
{
    if (!require_configured(s))
        return 0;

    if (!s->data_entered)
    {
        printf("\n[!] Allocation and request data have not been entered.\n");
        printf("    Use option 2 (Enter Resource Allocation and Request Data) first.\n");
        return 0;
    }
    return 1;
}

/* ================================================================
   CONFIGURATION AND DATA ENTRY
   ================================================================ */

/* Option 1: number of processes, resource types, instances per type */
static void configure_system(SystemState *s)
{
    print_header("CONFIGURE PROCESSES AND RESOURCES");

    if (s->configured)
        printf("[i] A configuration exists. Completing this step replaces it\n"
               "    and clears all allocation, request and recovery data.\n\n");

    char prompt[128];
    long num_p = 0, num_r = 0;
    long instances[MAX_RESOURCES] = {0};

    snprintf(prompt, sizeof(prompt), "Number of processes (1-%d): ", MAX_PROCESSES);
    if (!read_int_in_range(prompt, 1, MAX_PROCESSES, &num_p))
        return;

    snprintf(prompt, sizeof(prompt), "Number of resource types (1-%d): ", MAX_RESOURCES);
    if (!read_int_in_range(prompt, 1, MAX_RESOURCES, &num_r))
        return;

    for (int j = 0; j < (int)num_r; j++)
    {
        snprintf(prompt, sizeof(prompt),
                 "Total instances of R%d (1-%d): ", j, MAX_INSTANCES);
        if (!read_int_in_range(prompt, 1, MAX_INSTANCES, &instances[j]))
            return;                      /* abort: nothing was changed */
    }

    /* Everything was valid: commit the new configuration */
    reset_simulation(s);
    s->num_processes = (int)num_p;
    s->num_resources = (int)num_r;

    for (int i = 0; i < s->num_processes; i++)
        snprintf(s->process_name[i], NAME_LEN, "P%d", i);

    for (int j = 0; j < s->num_resources; j++)
    {
        snprintf(s->resource_name[j], NAME_LEN, "R%d", j);
        s->total[j]     = (int)instances[j];
        s->available[j] = (int)instances[j];
    }

    s->configured = 1;

    printf("\n[OK] Configuration saved: %d processes, %d resource types.\n",
           s->num_processes, s->num_resources);
    printf("     Process names are generated automatically (P0, P1, ...).\n");
    printf("     Next step: option 2 to enter allocation and request data.\n");
}

/*
 * Reads the Allocation matrix row by row. Each value is bounded by the
 * number of instances still unallocated, so the column sums can never
 * exceed Total[j]. Returns 1 on success, 0 on EOF (caller discards data).
 */
static int enter_allocation_data(SystemState *s)
{
    int  used[MAX_RESOURCES] = {0};
    char line[INPUT_BUFFER];

    print_header("ENTER ALLOCATION DATA");
    printf("Allocation[i][j] = instances of resource j that process i HOLDS now.\n");
    printf("Enter %d space-separated values per process (example: 1 0 2).\n",
           s->num_resources);

    for (int i = 0; i < s->num_processes; i++)
    {
        for (;;)
        {
            int max_values[MAX_RESOURCES];
            int row[MAX_RESOURCES];

            for (int j = 0; j < s->num_resources; j++)
                max_values[j] = s->total[j] - used[j];

            printf("\nUnallocated so far : ");
            for (int j = 0; j < s->num_resources; j++)
                printf("%s=%d  ", s->resource_name[j], max_values[j]);

            printf("\nAllocation held by %s: ", s->process_name[i]);
            fflush(stdout);

            if (!read_line(line, sizeof(line)))
            {
                printf("\n[!] End of input reached. Data entry aborted.\n");
                return 0;
            }

            if (!parse_row(line, s->num_resources, max_values, s, row))
                continue;               /* error already explained: retry row */

            for (int j = 0; j < s->num_resources; j++)
            {
                s->allocation[i][j] = row[j];
                used[j] += row[j];
            }
            break;
        }
    }

    return 1;
}

/*
 * Reads the Request matrix. A process cannot hold + request more than
 * exists, so Request[i][j] <= Total[j] - Allocation[i][j].
 */
static int enter_request_data(SystemState *s)
{
    char line[INPUT_BUFFER];

    print_header("ENTER REQUEST DATA");
    printf("Request[i][j] = ADDITIONAL instances of resource j that process i\n");
    printf("is currently waiting for. Enter 0 for resources it does not need.\n");
    printf("Enter %d space-separated values per process.\n", s->num_resources);

    for (int i = 0; i < s->num_processes; i++)
    {
        for (;;)
        {
            int max_values[MAX_RESOURCES];
            int row[MAX_RESOURCES];

            for (int j = 0; j < s->num_resources; j++)
                max_values[j] = s->total[j] - s->allocation[i][j];

            printf("\nOutstanding request of %s: ", s->process_name[i]);
            fflush(stdout);

            if (!read_line(line, sizeof(line)))
            {
                printf("\n[!] End of input reached. Data entry aborted.\n");
                return 0;
            }

            if (!parse_row(line, s->num_resources, max_values, s, row))
                continue;

            for (int j = 0; j < s->num_resources; j++)
                s->request[i][j] = row[j];
            break;
        }
    }

    return 1;
}

/*
 * Available[j] = Total[j] - sum_i Allocation[i][j]
 * Returns 0 (and leaves data untouched) if any column is over-allocated.
 */
static int calculate_available_resources(SystemState *s)
{
    int computed[MAX_RESOURCES];

    for (int j = 0; j < s->num_resources; j++)
    {
        int held = 0;
        for (int i = 0; i < s->num_processes; i++)
            held += s->allocation[i][j];

        computed[j] = s->total[j] - held;
        if (computed[j] < 0)
            return 0;
    }

    for (int j = 0; j < s->num_resources; j++)
        s->available[j] = computed[j];

    return 1;
}

/* Option 2: enter allocation and request data (all-or-nothing) */
static void enter_data_menu(SystemState *s)
{
    if (!require_configured(s))
        return;

    if (s->data_entered)
        printf("\n[i] Existing data will be replaced. Termination history is cleared.\n");

    clear_matrix_data(s);               /* nothing partial survives */

    if (!enter_allocation_data(s) || !enter_request_data(s))
    {
        clear_matrix_data(s);
        printf("[!] Data entry was not completed. No data has been stored.\n");
        return;
    }

    if (!calculate_available_resources(s))
    {
        clear_matrix_data(s);
        printf("[!] Internal check failed: allocations exceed totals. Data discarded.\n");
        return;
    }

    s->data_entered = 1;
    printf("\n[OK] Allocation and request data stored.\n");
    printf("     Available resources were calculated as Total - sum(Allocation).\n");
}

/* Consistency check used before detection / complete simulation */
static int validate_configuration(const SystemState *s)
{
    int ok = 1;

    if (!s->configured || !s->data_entered)
    {
        printf("[X] Configuration or data is missing.\n");
        return 0;
    }

    if (s->num_processes < 1 || s->num_processes > MAX_PROCESSES ||
        s->num_resources < 1 || s->num_resources > MAX_RESOURCES)
    {
        printf("[X] Process or resource count is out of range.\n");
        return 0;
    }

    for (int j = 0; j < s->num_resources; j++)
    {
        int held = 0;

        for (int i = 0; i < s->num_processes; i++)
        {
            if (s->allocation[i][j] < 0 || s->request[i][j] < 0)
            {
                printf("[X] Negative value for %s / %s.\n",
                       s->process_name[i], s->resource_name[j]);
                ok = 0;
            }
            if (s->terminated[i] &&
                (s->allocation[i][j] != 0 || s->request[i][j] != 0))
            {
                printf("[X] Terminated process %s still has data.\n",
                       s->process_name[i]);
                ok = 0;
            }
            held += s->allocation[i][j];
        }

        if (held > s->total[j])
        {
            printf("[X] %s is over-allocated (%d > %d).\n",
                   s->resource_name[j], held, s->total[j]);
            ok = 0;
        }
        else if (s->available[j] != s->total[j] - held)
        {
            printf("[X] Available[%s] is inconsistent with Total - Allocation.\n",
                   s->resource_name[j]);
            ok = 0;
        }
    }

    if (ok)
        printf("[OK] Configuration is valid and consistent.\n");

    return ok;
}

/* ================================================================
   DISPLAY FUNCTIONS
   ================================================================ */

static void print_vector(const int *values, int count)
{
    printf("[");
    for (int j = 0; j < count; j++)
        printf("%s%d", j == 0 ? "" : " ", values[j]);
    printf("]");
}

static void print_process_list(const SystemState *s, const int *ids, int count)
{
    if (count == 0)
    {
        printf("(none)");
        return;
    }
    for (int k = 0; k < count; k++)
        printf("%s%s", k == 0 ? "" : ", ", s->process_name[ids[k]]);
}

/* Prints Allocation (use_request = 0) or Request (use_request = 1) */
static void print_matrix(const SystemState *s, const char *title, int use_request)
{
    printf("\n%s\n", title);
    print_line();

    printf("%-9s", "Process");
    for (int j = 0; j < s->num_resources; j++)
        printf("%-6s", s->resource_name[j]);
    printf("Status\n");
    print_line();

    for (int i = 0; i < s->num_processes; i++)
    {
        printf("%-9s", s->process_name[i]);
        for (int j = 0; j < s->num_resources; j++)
            printf("%-6d", use_request ? s->request[i][j] : s->allocation[i][j]);
        printf("%s\n", s->terminated[i] ? "TERMINATED" : "ACTIVE");
    }
}

/* Option 3 */
static void display_system_state(const SystemState *s)
{
    print_header("CURRENT SYSTEM STATE");

    if (!s->configured)
    {
        printf("The system is not configured. Use option 1 first.\n");
        return;
    }

    int active = 0;
    for (int i = 0; i < s->num_processes; i++)
        if (!s->terminated[i])
            active++;

    printf("Processes      : %d (active: %d, terminated: %d)\n",
           s->num_processes, active, s->num_processes - active);
    printf("Resource types : %d\n\n", s->num_resources);

    printf("%-12s", "Resource");
    for (int j = 0; j < s->num_resources; j++)
        printf("%-6s", s->resource_name[j]);
    printf("\n%-12s", "Total");
    for (int j = 0; j < s->num_resources; j++)
        printf("%-6d", s->total[j]);

    if (!s->data_entered)
    {
        printf("\n\n[i] Allocation and request data not entered yet (option 2).\n");
        return;
    }

    printf("\n%-12s", "Available");
    for (int j = 0; j < s->num_resources; j++)
        printf("%-6d", s->available[j]);
    printf("\n");

    print_matrix(s, "ALLOCATION MATRIX (resources held)", 0);
    print_matrix(s, "REQUEST MATRIX (resources waited for)", 1);

    printf("\nLAST DETECTION RESULT\n");
    print_line();

    if (!s->last_detection.valid)
        printf("Detection has not been run on the current data.\n");
    else if (s->last_detection.deadlock_found)
    {
        printf("DEADLOCK DETECTED. Deadlocked processes: ");
        print_process_list(s, s->last_detection.deadlocked,
                           s->last_detection.deadlocked_count);
        printf("\n");
    }
    else
        printf("No deadlock detected.\n");

    if (s->history_count > 0)
    {
        printf("\nRECOVERY HISTORY\n");
        print_line();
        for (int k = 0; k < s->history_count; k++)
            printf("%d. Strategy %c terminated %s\n", k + 1,
                   s->history_strategy[k], s->process_name[s->history_pid[k]]);
    }
}

/* Prints a detection result (completion sequence, deadlocked set) */
static void display_detection_result(const SystemState *s, const DetectionResult *r)
{
    printf("\nDETECTION RESULT\n");
    print_line();

    if (r->idle_count > 0)
    {
        printf("Holding no resources (cannot block others): ");
        print_process_list(s, r->idle, r->idle_count);
        printf("\n");
    }

    if (r->sequence_length == 0)
        printf("Completion sequence : (no process could complete)\n");
    else
    {
        printf("Completion sequence : ");
        for (int k = 0; k < r->sequence_length; k++)
            printf("%s%s", k == 0 ? "" : " -> ", s->process_name[r->sequence[k]]);
        printf("\n");
    }

    if (!r->deadlock_found)
    {
        printf("\n[OK] NO DEADLOCK DETECTED - every process can run to completion.\n");
        return;
    }

    printf("\n[!!] DEADLOCK DETECTED\n");
    printf("Deadlocked processes (%d): ", r->deadlocked_count);
    print_process_list(s, r->deadlocked, r->deadlocked_count);

    printf("\n\nResources that can ever become free (Work) : ");
    print_vector(r->work_final, s->num_resources);
    printf("\n");

    for (int k = 0; k < r->deadlocked_count; k++)
    {
        int p = r->deadlocked[k];
        printf("  %-4s holds ", s->process_name[p]);
        print_vector(s->allocation[p], s->num_resources);
        printf(" and waits for ");
        print_vector(s->request[p], s->num_resources);
        printf("  -> request exceeds Work\n");
    }
}

/* ================================================================
   DEADLOCK DETECTION
   ================================================================ */

/*
 * detect_deadlock: Work / Finish algorithm for multiple instances.
 * The system state is read-only (const); all working data is local.
 *
 *   Work   = Available
 *   Finish[i] = true if terminated or holding nothing, else false
 *   while some i has Finish[i]==false and Request[i] <= Work:
 *         Work += Allocation[i];  Finish[i] = true;  record i
 *   Finish[i]==false at the end  =>  process i is deadlocked
 */
static void detect_deadlock(const SystemState *s, DetectionResult *result)
{
    int work[MAX_RESOURCES];
    int finish[MAX_PROCESSES];

    memset(result, 0, sizeof(*result));

    for (int j = 0; j < s->num_resources; j++)
        work[j] = s->available[j];

    for (int i = 0; i < s->num_processes; i++)
    {
        int holds_something = 0;

        for (int j = 0; j < s->num_resources; j++)
            if (s->allocation[i][j] > 0)
                holds_something = 1;

        if (s->terminated[i])
            finish[i] = 1;                       /* gone from the system   */
        else if (!holds_something)
        {
            finish[i] = 1;                       /* nothing to release     */
            result->idle[result->idle_count++] = i;
        }
        else
            finish[i] = 0;
    }

    int progress = 1;

    while (progress)
    {
        progress = 0;

        for (int i = 0; i < s->num_processes; i++)
        {
            if (finish[i])
                continue;

            /* can the pending request be satisfied for EVERY resource? */
            int can_run = 1;
            for (int j = 0; j < s->num_resources; j++)
                if (s->request[i][j] > work[j])
                {
                    can_run = 0;
                    break;
                }

            if (!can_run)
                continue;

            /* simulate process i finishing: it releases what it holds */
            for (int j = 0; j < s->num_resources; j++)
                work[j] += s->allocation[i][j];

            finish[i] = 1;
            result->sequence[result->sequence_length++] = i;
            progress = 1;
        }
    }

    for (int i = 0; i < s->num_processes; i++)
        if (!finish[i])
            result->deadlocked[result->deadlocked_count++] = i;

    for (int j = 0; j < s->num_resources; j++)
        result->work_final[j] = work[j];

    result->deadlock_found = (result->deadlocked_count > 0);
    result->valid = 1;
}

/* Option 4 */
static void menu_detect_deadlock(SystemState *s)
{
    if (!require_ready(s))
        return;

    print_header("DEADLOCK DETECTION");

    if (!validate_configuration(s))
    {
        printf("[!] Detection aborted: the system data is inconsistent.\n");
        return;
    }

    detect_deadlock(s, &s->last_detection);
    display_detection_result(s, &s->last_detection);
}

/* ================================================================
   DEADLOCK RECOVERY (simulated termination)
   ================================================================ */

/*
 * terminate_process: simulated kill of one process.
 *  - refuses if pid is invalid or already terminated (no double release)
 *  - copies its allocation to released[]
 *  - zeroes its allocation row and request row
 *  - marks it terminated, logs it, recomputes Available
 * Returns 1 on success, 0 on refusal.
 */
static int terminate_process(SystemState *s, int pid, char strategy, int *released)
{
    if (pid < 0 || pid >= s->num_processes)
        return 0;
    if (s->terminated[pid])
        return 0;

    for (int j = 0; j < s->num_resources; j++)
    {
        released[j] = s->allocation[pid][j];
        s->allocation[pid][j] = 0;
        s->request[pid][j] = 0;
    }

    s->terminated[pid] = 1;

    if (s->history_count < MAX_PROCESSES)
    {
        s->history_pid[s->history_count]      = pid;
        s->history_strategy[s->history_count] = strategy;
        s->history_count++;
    }

    /* Available is always rebuilt from Total - Allocation (never added
       to incrementally), so a resource can never be counted twice. */
    return calculate_available_resources(s);
}

/* Prints the outcome after recovery; returns remaining deadlocked count */
static int report_recovery_outcome(SystemState *s)
{
    printf("\nRe-running deadlock detection to verify the result...\n");

    detect_deadlock(s, &s->last_detection);
    display_detection_result(s, &s->last_detection);

    printf("\nAvailable resources now : ");
    print_vector(s->available, s->num_resources);
    printf("\n");

    if (s->last_detection.deadlock_found)
    {
        printf("\n[!!] RECOVERY INCOMPLETE: %d process(es) are still deadlocked.\n",
               s->last_detection.deadlocked_count);
        printf("     Further processes must be terminated to break the deadlock.\n");
    }
    else
        printf("\n[OK] VERIFIED: detection finds no deadlock. Deadlock resolved.\n");

    return s->last_detection.deadlocked_count;
}

/*
 * Strategy A: terminate ONE process.
 * Returns the number of still-deadlocked processes, or -1 on error.
 */
static int recover_by_terminating_process(SystemState *s, int pid)
{
    int released[MAX_RESOURCES];

    print_header("RECOVERY - STRATEGY A: TERMINATE ONE PROCESS");

    if (pid < 0 || pid >= s->num_processes)
    {
        printf("[X] Invalid process selection.\n");
        return -1;
    }
    if (s->terminated[pid])
    {
        printf("[X] %s is already terminated; nothing to release.\n",
               s->process_name[pid]);
        return -1;
    }

    if (!terminate_process(s, pid, 'A', released))
    {
        printf("[X] Termination of %s failed.\n", s->process_name[pid]);
        return -1;
    }

    printf("Terminating %s (simulated)...\n", s->process_name[pid]);
    printf("Resources released   : ");
    print_vector(released, s->num_resources);
    printf("\nRequest row of %s removed. %s marked TERMINATED.\n",
           s->process_name[pid], s->process_name[pid]);

    return report_recovery_outcome(s);
}

/*
 * Strategy B: terminate every process that detection currently reports
 * as deadlocked. Returns remaining deadlocked count, or -1 on error.
 */
static int recover_by_terminating_all_deadlocked(SystemState *s)
{
    DetectionResult before;
    int victims[MAX_PROCESSES];
    int victim_count;
    int released[MAX_RESOURCES];
    int total_released[MAX_RESOURCES] = {0};

    print_header("RECOVERY - STRATEGY B: TERMINATE ALL DEADLOCKED");

    detect_deadlock(s, &before);

    if (!before.deadlock_found)
    {
        printf("[OK] No deadlock exists. Nothing to terminate.\n");
        return 0;
    }

    victim_count = before.deadlocked_count;
    for (int k = 0; k < victim_count; k++)
        victims[k] = before.deadlocked[k];

    for (int k = 0; k < victim_count; k++)
    {
        if (!terminate_process(s, victims[k], 'B', released))
        {
            printf("[X] Could not terminate %s.\n", s->process_name[victims[k]]);
            return -1;
        }

        printf("Terminated %-4s released ", s->process_name[victims[k]]);
        print_vector(released, s->num_resources);
        printf("\n");

        for (int j = 0; j < s->num_resources; j++)
            total_released[j] += released[j];
    }

    printf("\nTotal resources released : ");
    print_vector(total_released, s->num_resources);
    printf("\n");

    return report_recovery_outcome(s);
}

/*
 * Lets the user pick a process from the CURRENT deadlocked list.
 * Returns the process index, or -1 if cancelled / EOF.
 */
static int select_deadlocked_process(const SystemState *s)
{
    char line[INPUT_BUFFER];

    for (;;)
    {
        printf("\nDeadlocked processes: ");
        print_process_list(s, s->last_detection.deadlocked,
                           s->last_detection.deadlocked_count);
        printf("\nEnter process number to terminate (e.g. 2 or P2), or -1 to cancel: ");
        fflush(stdout);

        if (!read_line(line, sizeof(line)))
            return -1;

        const char *p = line;
        while (*p != '\0' && isspace((unsigned char)*p))
            p++;
        if (*p == 'P' || *p == 'p')
            p++;

        long value = 0;
        int code = validate_input(p, -1, s->num_processes - 1, &value);

        if (code != INPUT_OK)
        {
            printf("[!] Invalid selection. Enter a process number from the list.\n");
            continue;
        }

        if (value == -1)
            return -1;

        int pid = (int)value;

        if (s->terminated[pid])
        {
            printf("[!] %s is already terminated.\n", s->process_name[pid]);
            continue;
        }

        int in_list = 0;
        for (int k = 0; k < s->last_detection.deadlocked_count; k++)
            if (s->last_detection.deadlocked[k] == pid)
                in_list = 1;

        if (!in_list)
        {
            printf("[!] %s is not in the deadlocked list.\n", s->process_name[pid]);
            continue;
        }

        return pid;
    }
}

/*
 * Interactive recovery loop used by option 5 and option 6.
 * Always starts with a fresh detection run. Repeats while the user
 * wants to continue and deadlocked processes remain.
 */
static void recovery_session(SystemState *s)
{
    int round = 0;

    while (!input_eof)
    {
        detect_deadlock(s, &s->last_detection);

        if (!s->last_detection.deadlock_found)
        {
            if (round == 0)
            {
                printf("\n[OK] No deadlock detected. Recovery is not required;\n");
                printf("     the system state was left unchanged.\n");
            }
            return;
        }

        print_header("DEADLOCK RECOVERY");
        printf("Deadlocked processes (%d): ", s->last_detection.deadlocked_count);
        print_process_list(s, s->last_detection.deadlocked,
                           s->last_detection.deadlocked_count);
        printf("\n\nRecovery strategies:\n");
        printf("  A. Terminate one selected deadlocked process\n");
        printf("  B. Terminate ALL currently deadlocked processes\n");
        printf("  C. Cancel (keep the state unchanged)\n");

        char line[INPUT_BUFFER];
        printf("\nChoose strategy (A/B/C): ");
        fflush(stdout);

        if (!read_line(line, sizeof(line)))
        {
            printf("\n[!] End of input reached. Recovery cancelled.\n");
            return;
        }

        const char *p = line;
        while (*p != '\0' && isspace((unsigned char)*p))
            p++;
        char choice = (char)toupper((unsigned char)*p);

        if (choice != 'A' && choice != 'B' && choice != 'C')
        {
            printf("[!] Invalid choice. Enter A, B or C.\n");
            continue;
        }

        if (choice == 'C')
        {
            printf("\nRecovery cancelled. The deadlock remains; state preserved.\n");
            return;
        }

        int remaining;

        if (choice == 'A')
        {
            int pid = select_deadlocked_process(s);
            if (pid < 0)
            {
                printf("\nSelection cancelled.\n");
                return;
            }
            remaining = recover_by_terminating_process(s, pid);
        }
        else
        {
            printf("\nThis will terminate ALL %d deadlocked process(es): ",
                   s->last_detection.deadlocked_count);
            print_process_list(s, s->last_detection.deadlocked,
                               s->last_detection.deadlocked_count);
            printf("\n");

            if (!ask_yes_no("Confirm termination? (y/n): "))
            {
                printf("Operation cancelled. State preserved.\n");
                return;
            }
            remaining = recover_by_terminating_all_deadlocked(s);
        }

        round++;

        if (remaining <= 0)
            return;                     /* resolved (0) or error (-1) */

        if (!ask_yes_no("\nDeadlock still present. Continue recovery? (y/n): "))
        {
            printf("Recovery stopped. Remaining deadlock reported above.\n");
            return;
        }
    }
}

/* Option 5 */
static void menu_recover(SystemState *s)
{
    if (!require_ready(s))
        return;

    print_header("RECOVER FROM DEADLOCK");

    if (!validate_configuration(s))
    {
        printf("[!] Recovery aborted: the system data is inconsistent.\n");
        return;
    }

    recovery_session(s);
}

/* ================================================================
   COMPLETE SIMULATION
   ================================================================ */

static void print_final_summary(const SystemState *s)
{
    int terminated = 0;
    for (int i = 0; i < s->num_processes; i++)
        if (s->terminated[i])
            terminated++;

    print_header("FINAL SYSTEM SUMMARY");

    printf("Processes terminated : %d of %d\n", terminated, s->num_processes);
    printf("Available resources  : ");
    print_vector(s->available, s->num_resources);
    printf("\n");

    if (s->last_detection.deadlock_found)
    {
        printf("Final status         : DEADLOCKED - ");
        print_process_list(s, s->last_detection.deadlocked,
                           s->last_detection.deadlocked_count);
        printf(" cannot proceed.\n");
    }
    else
        printf("Final status         : DEADLOCK-FREE\n");
}

/* Option 6: full workflow on the user's own data */
static void run_complete_simulation(SystemState *s)
{
    if (!require_ready(s))
        return;

    print_header("COMPLETE SIMULATION");

    printf("STEP 1: Validate configuration\n");
    if (!validate_configuration(s))
    {
        printf("[!] Simulation stopped: please correct the data (option 2).\n");
        return;
    }

    printf("\nSTEP 2: Initial system state\n");
    display_system_state(s);

    printf("\nSTEP 3: Deadlock detection\n");
    detect_deadlock(s, &s->last_detection);
    display_detection_result(s, &s->last_detection);

    if (!s->last_detection.deadlock_found)
    {
        printf("\nSTEP 4: Recovery not needed - the system is deadlock-free.\n");
    }
    else
    {
        printf("\nSTEP 4: Recovery\n");

        if (ask_yes_no("Deadlock detected. Start recovery? (y/n): "))
            recovery_session(s);
        else
            printf("\nRecovery skipped. The original state is preserved.\n");
    }

    printf("\nSTEP 5: Final verification\n");
    detect_deadlock(s, &s->last_detection);     /* read-only re-check */
    display_system_state(s);
    print_final_summary(s);
}

/* ================================================================
   MAIN
   ================================================================ */

int main(void)
{
    long choice = 0;

    reset_simulation(&simulation);
    print_banner();

    while (1)
    {
        display_main_menu();

        if (!read_int_in_range("\nEnter choice: ", 0, 7, &choice))
        {
            printf("Exiting simulator.\n");
            return 0;
        }

        switch (choice)
        {
        case 1:
            configure_system(&simulation);
            break;

        case 2:
            enter_data_menu(&simulation);
            break;

        case 3:
            display_system_state(&simulation);
            break;

        case 4:
            menu_detect_deadlock(&simulation);
            break;

        case 5:
            menu_recover(&simulation);
            break;

        case 6:
            run_complete_simulation(&simulation);
            break;

        case 7:
            reset_simulation(&simulation);
            printf("\n[OK] Simulation reset. All data, statuses, detection results\n"
                   "     and recovery history were cleared. Use option 1 to start.\n");
            break;

        case 0:
            printf("\nThank you for using the Deadlock Detection and Recovery Simulator.\n");
            return 0;

        default:
            printf("Invalid choice.\n");
            break;
        }

        if (input_eof)
        {
            printf("\nInput ended. Exiting simulator.\n");
            return 0;
        }
    }

    return 0;
}