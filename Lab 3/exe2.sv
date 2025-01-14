//------------------------------String---------------------------------//
module string_name;
  	// Declare the Inputs
    string s = "Tran Duc Manh";
    int value;
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
      	$display("4th character of the string: |%c|",  s.getc(4));
      	$display("String: %s", s);
		
      	// Put a character at 5th position and re-display the string
      	s.putc(5, "S");
        $display("String after put a character at 5th position: %s", s);

      	// Delete 7th character in the string
      	s = {s.substr(0,6), s.substr(8,12)};
        $display("String after deleting 7th character: %s", s);
      
      	// Print binary value in the string
        foreach(s[i]) begin
          $display("String value at %0d is %b", i, s[i]);
        end
      
      	// Extract value and store in integer
        s = "12578_123_12abcd";
        value = s.atoi();
        $display("Integer Value: %d", value);

        // Store equivalent string representation of the value in a user defined string.
      	value = 5678;
      	s.itoa(value);
        $display("String Value: %s", s); 
      	$finish;
    end
endmodule