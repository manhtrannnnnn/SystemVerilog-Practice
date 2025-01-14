//---------------------------------------------Interface---------------------------------------------//
interface arb_if;
    logic [3:0] a, b;
    logic a_greater_b, a_equal_b, a_less_b;

    // Modports for different roles
    modport DUT(
        input a, b,
        output a_greater_b, a_equal_b, a_less_b
    );

    modport TEST(
        output a, b,
        input a_greater_b, a_equal_b, a_less_b
    );

    modport MONITOR(
        input a, b,
        input a_greater_b, a_equal_b, a_less_b
    );
endinterface

//---------------------------------------------DUT---------------------------------------------//
module comparator(arb_if.DUT arbif);
    assign arbif.a_greater_b = (arbif.a > arbif.b);
    assign arbif.a_equal_b = (arbif.a == arbif.b);
    assign arbif.a_less_b = (arbif.a < arbif.b);
endmodule

//---------------------------------------------Testbench---------------------------------------------//
module comparator_tb(arb_if.TEST arbif);
    // Task to generate random inputs
    task random_input();
        forever begin
            arbif.a = $urandom_range(0, 15);
            arbif.b = $urandom_range(0, 15);
            #3;
            $display("[TIME: %0t] Random Input || a: %b, b: %b || A > B: %b, A = B: %b, A < B: %b",
                     $time, arbif.a, arbif.b, arbif.a_greater_b, arbif.a_equal_b, arbif.a_less_b);
        end
    endtask

    // Task to generate directed inputs
    task directed_input();
        forever begin
            arbif.a = 4'b1011; // Example directed input
            arbif.b = 4'b1001; // Example directed input
            #2;
            $display("[TIME: %0t] Directed Input || a: %b, b: %b || A > B: %b, A = B: %b, A < B: %b",
                     $time, arbif.a, arbif.b, arbif.a_greater_b, arbif.a_equal_b, arbif.a_less_b);
        end
    endtask

    process p1, p2;

    // Simulation control
    initial begin
       
        fork
            // Thread 1: Random 
            begin
                p1 = process :: self();
                random_input();
            end

            // Thread 2
            begin
                p2 = process :: self();
                directed_input();
            end

            // Thread 3: Control
            begin
                #0; p2.suspend();
                #100; p2.resume(); p1.suspend();
                #20; p1.resume(); p2.suspend(); 
            end
        join_none


        #1000;
        p1.kill();
        p2.kill();
        $finish; // End simulation at 1000 time units
    end

    // Final block to display end of simulation message
    final begin
        $display("===========================================");
        $display("End of Simulation at time %t", $time);
        $display("===========================================");
    end
endmodule

//---------------------------------------------Top---------------------------------------------//
module top;
    // Instantiate the interface
    arb_if arbif();

    // Instantiate the DUT
    comparator u_comparator(.arbif(arbif.DUT));

    // Instantiate the testbench
    comparator_tb u_tb(.arbif(arbif.TEST));

    initial begin
        $dumpfile("dump.vcd");
        $dumpvars(0, top);
    end
endmodule
