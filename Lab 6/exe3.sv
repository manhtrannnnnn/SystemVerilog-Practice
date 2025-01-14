//--------------------------------------------Exercise 3--------------------------------------------//
module exe3;
    int var1, var2;
    event ev_1, ev_2;

    initial begin
        fork
            // Thread 1
            forever begin
                #5; // Delay for thread execution
           		@ev_2; // Wait for ev_2
              	$display("[Thread 1: %0t] Waiting for ev_2", $time);
                ->ev_2;
              	$display("[Thread 1: %0t] ev_2 triggered, var2 = %0d ", $time, var2);
            end

            // Thread 2
            	forever begin
                #10; // Delay for thread execution
                var2 = $random % 256; // Assign random value to var2
                $display("[Thread 2: %0t] Assigning random value to var2 = %0d at time %0t", $time, var2);
                ->ev_2; // Trigger ev_2
                $display("[Thread 2: %0t] ev_2 triggered", $time);
                $display("[Thread 2: %0t] Waiting for ev_1", $time);
                @ev_1; // Wait for ev_1
              	$display("[Thread 2: %0t] ev_1 triggered, var1 = %0d", $time, var1);
            end
        join_none

        #20;
        ->ev_1;

        #50;
        $finish;
    end
endmodule


