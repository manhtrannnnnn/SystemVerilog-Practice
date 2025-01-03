//-----------------------------------Enum Calender-----------------------------------//
module enum_calender;
    typedef enum int { January, February, March = 5, April, May, June, July, August, September = 15, Octorber, November, December} month;
    month current_month;
    initial begin
        // Assign integer value to the month enum-variable(try in range and out of range)
        $display("-----------------Assign integer value to the month enum-variable-----------------");
        current_month = month'(1);
      	$display("Current month: %s", current_month.name());
        current_month = month'(18);
      	$display("Current month: %s", current_month.name());
      	current_month = month'(19);
      	$display("Current month: %s", current_month.name());
      
      	// Assign June to enum variable
      	current_month = June;
        $display("-----------------Assign June to enum variable-----------------");
        $display("Current month: %s", current_month.name());

        // Declare an int type variable and update it with value enum - variable + 3
        $display("-----------------Update enum-variable with value of enum-variable + 3-----------------");
        current_month = month'(current_month + 3);
      	$display("Current month: %d", current_month);
        $finish;
    end
endmodule