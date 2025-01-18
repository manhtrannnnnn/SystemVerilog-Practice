//----------------------------------------BASE CLASS----------------------------------------//
class packet #(parameter type DATA_TYPE = int);
    protected DATA_TYPE length;
    bit [1:0] saddr;
    bit [1:0] daddr;
    protected DATA_TYPE data[];

    local int val = 0;
  	static int static_ctr  = 0;
    int ctr = 0;

    // Constructor
    function new(DATA_TYPE length = 10);
        this.length = length;
      	this.data = new[this.length];
    endfunction

    // Randomize data
    task random();
        foreach (this.data[i]) begin
            this.data[i] = $random % 128; 
        end
    endtask

    // Set source and destination 
    function void set_addr(bit [1:0] saddr, bit [1:0] daddr);
        this.saddr = saddr;
        this.daddr = daddr;
        if (this.saddr == this.daddr) begin
            do this.daddr = $random % 4;
            while (this.saddr == this.daddr);
        end
    endfunction

    // Set local value
  	function void set_val(int val);
      this.val = val;
    endfunction

    // Get local value
    function int get_val;
      return this.val;
    endfunction

    // Static data testing
    function void global_value_testing();
        static_ctr++;
        ctr++;
    endfunction

    // Display
    virtual function void display();
      $display("Global Value: %0d, Local Value: %0d, Length: %d, Source Address: %b, Destination Address: %b, Data: %p", static_ctr, ctr,
                 this.length, this.saddr, this.daddr, this.data);
    endfunction
endclass

//----------------------------------------Inheritance - SUB CLASS----------------------------------------//
class inherit_packet extends packet#(int);

  // Construction
  	function new(DATA_TYPE length = 10);
      	super.new(length);
      	$display("Constructor from Sub Class");
    endfunction

    function void display();
      $display("Display from Subclass");
    endfunction
  

endclass

//----------------------------------------MODULE----------------------------------------//
module exe1;
  
    int tmp = 0;
    // Declare packet objects 
    packet int_packet;
    packet #(bit [7:0]) bit7_packet;
    packet #(bit [3:0]) bit_4packet;

    // Inheritance
    inherit_packet inherit_pkg;

    initial begin
        // Declare int parameter
        int_packet = new(5);
      	int_packet.random();
        int_packet.set_addr(2'b10, 2'b01);
        int_packet.display();
        

        // Declare 8 bits parameter
        bit7_packet = new(4);
        bit7_packet.random();
        bit7_packet.set_addr(2'b01, 2'b10);
      	bit7_packet.display();

      	// Display the value
        bit_4packet = new(3);
        bit_4packet.random();
        bit_4packet.set_addr(2'b11, 2'b11); // The same saddr and daddr;
        bit_4packet.display();

        // Set and Get Local Value
        int_packet.set_val(30'd120);
        tmp = int_packet.get_val();
        $display("Value of local value: %0d", tmp);
        $display("Value of public value: %0b", int_packet.saddr);

        // Inheritance 
        inherit_pkg = new();
        inherit_pkg.random();
        inherit_pkg.display();
      	inherit_pkg.set_val(20);
        tmp = inherit_pkg.get_val();
        $display("Value of local value: %0d", tmp);
        $display("Value of public value: %0b", inherit_pkg.saddr);
        inherit_packet.display();

        // Static variable
        int_packet.global_value_testing();
        int_packet.global_value_testing();
        int_packet.global_value_testing();
        int_packet.global_value_testing();
        int_packet.global_value_testing();
        int_packet.global_value_testing();
        int_packet.global_value_testing();

        int_packet.display();
        bit7_packet.display();
        bit_4packet.display();
    end
endmodule
