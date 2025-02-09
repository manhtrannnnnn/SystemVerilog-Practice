//----------------------------------------BASE CLASS----------------------------------------//
virtual class packet #(parameter type DATA_TYPE = int);

    DATA_TYPE length;
    bit [1:0] saddr;
    bit [1:0] daddr;
    DATA_TYPE data[];

    local int local_val = 0;
    protected int protected_val = 0;

    static int static_ctr  = 0;
    int ctr = 0;

    // Constructor
    function new(DATA_TYPE length);
        this.length = length;
        data = new[this.length];
    endfunction

    // Randomize data 
    pure virtual function void random();

    // Set source and destination
    pure virtual function void set_addr(bit [1:0] saddr, bit [1:0] daddr);

    // Set local value
    function void set_local_val(int local_val);
        this.local_val = local_val;
    endfunction

    // Get local value
    function int get_local_val();
        return this.local_val;
    endfunction

    // Static data testing
    function void global_value_testing();
        static_ctr++;
        ctr++;
    endfunction

    // Display packet details 
    pure virtual function void display();

endclass

//----------------------------------------Inheritance - SUB CLASS----------------------------------------//
class inherit_packet1 #(type DATA_TYPE = int) extends packet#(DATA_TYPE);

    // Constructor
    function new(DATA_TYPE length = 10);
        super.new(length);
    endfunction

    // Override random
    function void random();
        foreach (this.data[i]) begin
            this.data[i] = $random % 128; 
        end
    endfunction

    // Override set_addr
    virtual function void set_addr(bit [1:0] saddr, bit [1:0] daddr);
        this.saddr = saddr;
        this.daddr = daddr;
        if (this.saddr == this.daddr) begin
            do this.daddr = $random % 4;
            while (this.saddr == this.daddr);
        end
    endfunction

    // Set protected value
    function void set_protected_value(int protected_val = 0);
        this.protected_val = protected_val;
    endfunction

    // Get protected value
    function int get_protected_value(int protected_val = 0);
        return this.protected_val;
    endfunction

    // Override display
    function void display();
        $display("[TIME: %0t] [Inheritance 1]Global Value: %0d, Local Value: %0d, Length: %d, Source Address: %b, Destination Address: %b, Data: %p",
                 $time, this.static_ctr, this.ctr, this.length, this.saddr, this.daddr, this.data);
    endfunction
endclass

//----------------------------------------Inheritance - SUB CLASS----------------------------------------//
class inherit_packet2 #(type DATA_TYPE = int) extends packet#(DATA_TYPE);

    // Constructor
    function new(DATA_TYPE length = 10);
        super.new(length);
    endfunction

    // Override random
    function void random();
        foreach (this.data[i]) begin
            this.data[i] = i; 
        end
    endfunction

    // Override set_addr
    virtual function void set_addr(bit [1:0] saddr, bit [1:0] daddr);
        this.saddr = saddr;
        this.daddr = daddr;
        if (this.saddr == this.daddr) begin
            do this.daddr = $random % 4;
            while (this.saddr == this.daddr);
        end
    endfunction

     // Set protected value
    function void set_protected_value(int protected_val = 0);
        this.protected_val = protected_val;
    endfunction

    // Set get value
    function int get_protected_value(int protected_val = 0);
        return this.protected_val;
    endfunction

    // Override display
    function void display();
        $display("[TIME: %0t] [Inheritance 2] Global Value: %0d, Local Value: %0d, Length: %d, Source Address: %b, Destination Address: %b, Data: %p",
                 $time, this.static_ctr, this.ctr, this.length, this.saddr, this.daddr, this.data);
    endfunction
endclass

//----------------------------------------MODULE----------------------------------------//
module exe1;

    // Declare packet objects
    packet #(int) int_pkg; 
    packet #(int) bit7_pkg; 
    packet #(int) bit4_pkg;

    // Declare inheritance packet objects
    inherit_packet1 #(int) inherit_int_packet;
    inherit_packet2 #(int) inherit_bit7_packet;
    inherit_packet1 #(int) inherit_bit4_packet;

    // Mailbox and Semaphore
    mailbox pkt_mailbox;
    semaphore arbiter;

    int tmp = 0;

    initial begin
        // Initialize objects, mailbox and semaphore
        pkt_mailbox = new();
        arbiter = new(1);

        inherit_int_packet = new(5); 
        inherit_bit7_packet = new(4);
        inherit_bit4_packet = new(3);

        int_pkg = inherit_int_packet;
        bit7_pkg = inherit_bit7_packet;
        bit4_pkg = inherit_bit4_packet;

        // Testing local and protected
        inherit_int_packet.set_local_val(10);
        tmp = inherit_int_packet.get_local_val();
        $display("%0d", tmp);

        inherit_int_packet.set_protected_value(20);
        tmp = inherit_int_packet.get_protected_value();
        $display("%0d", tmp);

        // Declare int parameter packet from base class
        int_pkg.random();
        int_pkg.set_addr(2'b10, 2'b01);
        int_pkg.global_value_testing();
        pkt_mailbox.put(int_pkg); 

        // Declare 8-bit parameter packet
        bit7_pkg.random();
        bit7_pkg.set_addr(2'b01, 2'b10);
        bit7_pkg.global_value_testing();
        pkt_mailbox.put(bit7_pkg);

        // Declare 4-bit parameter packet
        bit4_pkg.random();
        bit4_pkg.set_addr(2'b11, 2'b11); // Same saddr and daddr
        bit4_pkg.global_value_testing();
        pkt_mailbox.put(bit4_pkg);

        // Semaphore arbiter for accessing packets
        fork
            process_packet();
            process_packet();
            process_packet();
        join
    end

    // Task to process packets
    task process_packet();
        packet pkt;
        arbiter.get(1); 
        pkt_mailbox.get(pkt); 
        pkt.display(); 
        #10;
        arbiter.put(1); 
    endtask
endmodule


