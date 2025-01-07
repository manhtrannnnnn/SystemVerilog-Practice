//-----------------------------------------Static and Automatic Variables-----------------------------------------//

module static_automatic;

    // Increment1 
    task increment1();
        static int count1 = 0;
        for(int i = 0; i < 8; i++) begin
            count1 = count1 + 1;
            $display("Static Count: %0d", count1);
        end
    endtask

    // Increment2
    task increment2();
        automatic int count2 = 0;
        for(int i = 0; i < 8; i++) begin
            count2 = count2 + 1;
            $display("Automatic Count: %0d", count2);
        end
    endtask

    initial begin
        $display("-----------------Static Variables-----------------");
        increment1();   // First time
      	increment1();   // Second time  
      	increment1();   // Third time
      	increment1();   // Fourth time
      
        $display("-----------------Automatic Variables-----------------");
        increment2();   // First time
        increment2();   // Second time
        increment2();   // Third time
        increment2();   // Fourth time    
        $finish;
    end
endmodule