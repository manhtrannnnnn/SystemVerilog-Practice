//------------------------------String---------------------------------//
module string_name;
  	// Declare the Inputs
    string s = "Tran Duc Manh";
    initial begin

        // Print the result
        $display("String: %s", s);

        // Print the size of the string
        $display("Size of string: %d", s.len());
        
        // Print Last Name using substr()
      	$display("Last Name: %s",  s.substr(9,12));
      
      	// Convert string to upper case
        $display("Upper Case: %s",  s.toupper());   

        // 5th character of the string and char
      	$display("4th character of the string: %c",  s.getc(5));
      	$display("String: %s", s);
		
      	// Put a character at 5th position and re-display the string
      
      	// Delete 7th character in the string
//         s = s.delete(7);
//         $display("String: %s", s);

      
      	// Print binary value in the string
      	$display("String Value: %b", s);
      
      	// Extract value and store in integer
        int value;
        value = s.atoi();
        $display("Integer Value: %d", value);
      	
      	$finish;
    end
endmodule